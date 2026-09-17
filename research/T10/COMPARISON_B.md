# T10 draft B comparison

This table compares the manuscript notions with the declarations in
`research/T10/DraftB.lean`. The draft keeps the physical (P) realization as
unit-periodic fields on `R^3`, but puts Sobolev analysis on complete Fourier
coefficient data.

## Paper notion to Lean definition

| Paper notion | Lean declaration | Exact choice |
|---|---|---|
| Unit torus and lattice | `PeriodicTorus`, `PeriodicFrequency` | `UnitAddTorus (Fin 3)` and `Fin 3 → ℤ`. Haar measure is the probability measure, so the fundamental cube has volume one. |
| Physical periodic field (P) | `IsPeriodicSpatial`, `IsPeriodicOn` | A field on `EuclideanSpace ℝ (Fin 3)` is invariant under each positive unit coordinate shift. All points are quantified, so negative shifts follow. For spacetime fields the quantifier order is `∀ t ∈ I, ∀ x, ∀ i`. |
| Passage from (P) to `T³` | `torusLift` | Restates `NSFormalization.Paper1.torusLift` from `Paper1/TorusCube.lean`: use Mathlib's measurable representative in `(0,1]^3`, then the inverse Euclidean-space coordinate equivalence. |
| Fourier coefficient | `periodicFourierCoeff` | Restates `NSFormalization.Paper1.periodicFourierCoeff`: `UnitAddTorus.mFourierCoeff (torusLift f) k`. Thus the character is the unit-period convention `exp(-2π i k·x)`. |
| Bessel weight | `periodicFrequencyWeight` | Exactly `1 + 4π² ∑_i k_i²`, not `1+|k|²` and not an angular-frequency weight without `2π`. The datum contains the square-root power `(weight)^(s/2)`. |
| Scalar coefficient space | `PeriodicScalarData` | Mathlib `lp (fun _ : (Fin 3 → ℤ) ↦ ℂ) 2`. |
| Real vector-valued coefficient space | `PeriodicVectorData`, `realPeriodicSubmodule`, `PeriodicSobolev s` | Three complex coefficient sequences with the `PiLp 2` product norm, restricted to `A_i(-k)=conj(A_i(k))`. Coefficients are complex because Fourier coefficients of real fields are generally complex; “real” means conjugate-reflection symmetry. The order `s` is a phantom realization index, just as the Section 4 datum carrier records which inverse weight is intended. |
| Coefficient norm | `periodicSobolevDataNorm` | The inherited `PiLp 2` of `lp 2` norm, hence the square root of the sum over all three components and all frequencies. |
| Physical field ↔ datum bridge | `IsPeriodicDatum` | Requires physical unit periodicity, then `∀ i, ∀ k`, `A_i(k) = (1+4π²|k|²)^(s/2) ẑ_i(k)`. It uses the exact `periodicFourierCoeff` above. |
| Physical `H^s(T³)` norm | `periodicSobolevENorm` | Infimum in `ℝ≥0∞` over representing real data. No datum gives the empty infimum `⊤`; uniqueness is a lemma, not part of the definition. |
| Spatial mean | `meanT`, `pressureMeanT` | Bochner integral against normalized Haar measure of `torusLift`. For pressure the definition is slice-by-slice. |
| Mean-zero field/decomposition | `IsMeanZeroT`, `constantPartT`, `meanZeroPartT`, `meanDecompositionT` | The canonical pair is `(x ↦ meanT z, x ↦ z x - meanT z)`. Its reconstruction and vanishing remainder mean are lemma obligations. |
| Mean-zero coefficient subspace | `meanZeroPeriodicSobolev` | Exactly `A_i(0)=0` for every component. Since the Bessel weight is one at zero, this is independent of `s`. |
| Solenoidal coefficient datum | `IsSolenoidalPeriodicDatum` | `∑_j (2π i k_j) A_j(k)=0` at every `k`. The scalar Sobolev weight commutes with this condition. |
| Periodic Leray projector | `periodicLeray`, `IsPeriodicLerayDatum` | Identity at `k=0`; otherwise `A_i-k_i(k·A)/|k|²`. `periodicLeray` is the exact coefficient formula and `IsPeriodicLerayDatum A B` is its graph inside the real weighted `ℓ²` carrier. Same-space existence and contraction are intentionally lemmas, not assumptions hidden in the definition. |
| Force Sobolev path and norm | `IsPeriodicSobolevPath`, `forceSobolevENormT` | At every `t≥0` the physical slice has datum `G t`; paths in the infimum are strongly measurable. The norm is Mathlib `eLpNorm` over `volume.restrict (Ioi 0)`. The all-times bridge is stronger than an a.e. bridge but agrees on the smooth force class. |
| Initial class `X_T` | `initialClassT` | Globally smooth physical lift, unit spatial periods, and pointwise zero divergence. There is no mean-zero condition: the paper allows nonzero spatial mean. |
| Force class `F_T` | `MemForceT`, `forceClassT` | Globally smooth physical lift, unit spatial periods, and a compact time-support set `K ⊂ (0,∞)` with `tsupport f ⊆ K × R³`. Spatial support is not compact in the periodic lift. This matches the local `PeriodicForceSpace.IsTestForce` shape but is restated for a future contract. |
| Pressure gauge | `PressureGaugeT` | `∀ t ∈ I, ∫_T³ p(t)=0`; pressure is also required to be periodic in `ClassicalSolutionT`, excluding affine representatives. |
| Classical solution | `ClassicalSolutionT` | A new contract structure, not the local `PeriodicLifespan.Flow`. It mirrors `ClassicalSolutionR` but adds periodic velocity, periodic pressure, and the zero-mean pressure gauge, and replaces whole-space Sobolev data by periodic coefficient data. The PDE remains the shared physical residual. A later binding needs explicit conversions to/from the local structure because structures cannot be connected by `rfl`. |
| Maximal lifespan | `maximalLifespanT` | `⨆ S, ⨆ (_ : Nonempty (ClassicalSolutionT ν a f S)), ENNReal.ofReal S`. Global lifespan is `⊤`; no solution gives `0`. Input-class hypotheses belong to consumers. |
| Regular through `T` | `RegularThroughT` | `∃ δ>0`, a classical solution exists to horizon `T+δ`. |
| Breakdown set `B_{ν,a,T}` | `breakdownSetInT`, `breakdownSetT` | Ambient-class form `{f∈Y : maximalLifespanT ν a f ≤ ofReal T}`, then `Y=forceClassT`. This is breakdown by `T`, not necessarily exactly at `T`. |
| Relative topology/density | `RelativelyDenseT` | Approximation form with exact order `∀ g∈Y, ∀ r>0, ∃ f∈S`, measured by `forceSobolevENormT q s (f-g)`. Section 3 later instantiates `q=1`. |
| Energy space `E_T` | `energyEssSupT`, `energyGradientT`, `energyENormT` | Haar-space `L²` norms and the open time interval `(0,T)`: `L∞_tL²_x + L²_tL²_x` of the full spatial gradient. Values are in `ℝ≥0∞`; no endpoint value at `T` is imposed. |

## Deliberate choices

- Weight normalization keeps the manuscript's `2π` exactly. The local
  `PeriodicSobolev.periodicFrequencyWeight` uses an equivalent complex-norm
  spelling; a binding lemma should identify it with this real sum.
- The carrier is real in the Fourier sense, not by pretending that Fourier
  coefficients are real. Its three components use a Euclidean product norm,
  not a supremum norm.
- Physical periodicity is a proposition on unbundled functions on `R³`, matching
  the repository's (P) layer. The torus is used only for coefficients and Haar
  integrals.
- `ClassicalSolutionT` is a new contract structure. Reusing the local
  `PeriodicLifespan.Flow` would violate the future contract import policy and
  would omit the coefficient-path field and pressure gauge from the stable
  statement.
- The Leray symbol is specified as a coefficient function plus a graph
  predicate on data. This avoids putting a contraction proof into a
  statements-only file while fixing every coefficient, including `k=0`.
- As in `Contracts/V1/Data.lean`, extended norms are never passed through
  `ENNReal.toReal`; infinite quantities therefore cannot satisfy finite-radius
  inequalities vacuously.

## Ambiguities and scope boundaries

- The paper defines `H^s(T³)` for periodic distributions. This contract's
  physical side is an actual real field, because T10 consumers are smooth
  initial data, smooth forces, and classical velocity slices. Negative-order
  distributional completion elements live on the coefficient side; an
  arbitrary periodic distribution is not separately bundled here.
- `UnitAddTorus.mFourierCoeff` is a totalized Bochner integral. A pathological
  nonintegrable physical slice could receive junk zero coefficients. Every
  slice in `initialClassT`, `forceClassT`, and `ClassicalSolutionT` is smooth on
  a compact torus, so this case is unreachable in the intended API.
- `IsPeriodicDatum` asks for a datum at every time in
  `IsPeriodicSobolevPath`, while Bochner paths are identified a.e. This is the
  same smooth-class-safe strengthening used by the Section 4 contract.
- `ContDiff ℝ ∞ f` plus compact positive time support treats a force as its
  smooth zero extension to all real times. This is equivalent to
  `C_c∞(T³×(0,∞))`, but stronger-looking than a function whose declared domain
  is only positive time.
- `PressureGaugeT` is required on `[0,T)`, including time zero. The PDE is
  imposed only for `0<t<T`, following `ClassicalSolutionR` and the shared
  residual's two-sided temporal derivative.
- The energy quantities, like their Section 4 counterparts, do not separately
  demand measurability. They are used on smooth fields, where measurability is
  automatic.
- `maximalLifespanT` is a supremum over existence, not a bundled uniqueness
  theorem. T11 must prove local uniqueness before interpreting this supremum as
  the unique maximal solution's lifespan.

## Needs a lemma

The following facts are intentionally not proofs or fields of this data
contract. T11 and later nodes will need them.

1. `torusLift` is measurable/continuous for continuous periodic fields, and
   Haar integration of `torusLift` equals the original unit-cube integral.
2. Scalar and three-vector Parseval, including equality of the coefficient
   `s=0` norm with physical `L²(T³)` and the gradient identity with factors
   `2π k`.
3. Positivity and evenness of `periodicFrequencyWeight`, equivalence with the
   local weight, and uniqueness/injectivity of `IsPeriodicDatum`.
4. Smooth periodic fields have a datum at every real order needed here;
   smooth time paths give continuous integer-order datum paths and strongly
   measurable force paths.
5. The zero Fourier coefficient equals `meanT`; `meanZeroPartT` has zero mean;
   `z = constantPartT z + meanZeroPartT z`; the two modes are orthogonal; and
   removing the zero mode cannot increase any `H^s` norm.
6. The Leray formula defines a member of `PeriodicSobolev s`, preserves the
   conjugate-reflection condition, is self-adjoint and idempotent, is the
   identity at zero, produces `IsSolenoidalPeriodicDatum`, fixes solenoidal
   data, and is a contraction on every `H^s`.
7. The periodic Leray projector commutes with derivatives, Bessel weights,
   `Λ`, and the periodic heat multiplier.
8. Pressure normalization by subtraction of `pressureMeanT` preserves
   periodicity, smoothness, and the momentum equation; the zero-mean periodic
   pressure representative is unique.
9. The mean evolution identity `m'(t)=meanT (f(t,·))`; consequently a
   mean-zero initial velocity stays mean zero when the force has zero mean.
   For general force, the decomposition used in Section 3 satisfies the exact
   mean-free equation with constant transport.
10. Spectral gap/Poincaré on `meanZeroPeriodicSobolev`, equivalence of
    homogeneous and inhomogeneous norms there, and Sobolev-order monotonicity.
11. Every `MemForceT` has finite `L^1_tH^m_x` and `L^2_tH^m_x` norms for each
    integer `m`, and its coefficient path can be chosen smooth.
12. The Haar-integral definition of `energyENormT` equals its coefficient-side
    Parseval formula and is equivalent, for fixed finite `T`, to the usual norm
    on `L∞_tL²_x ∩ L²_tH¹_x`.
13. Explicit forward/backward conversions between `ClassicalSolutionT` and the
    local periodic flow structure, with round-trip lemmas and equality of the
    resulting maximal-lifespan predicates.

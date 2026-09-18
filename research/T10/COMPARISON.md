# T10 periodic data layer — reconciled comparison

This comparison merges blind Draft A (lane 263) and blind Draft B (lane 264)
under the binding rulings in the lead's `research/T10/RECONCILIATION.md`.
`Spec.lean` is based on B, with A's more precise citations and proof-obligation
inventory, plus the reconciled homogeneous datum and consumer-facing API.

Registered: `T01.torus_data` (V1), containing the definitions through
`IsPeriodicReweight` plus `IsPeriodicOn` and the first ten proved data-layer
fields.  The solution-class portion of this comparison is deferred to T11.

## Authoritative definitions of `𝒳_𝕋` and `𝓕_𝕋`

The requested grep finds the definitions in `paper/sections/02-preliminaries.tex`,
not in `03-torus.tex`; the latter only says at lines 2--4 that it reuses them.
The decisive text is:

> `02-preliminaries.tex:9`:
> `\XX=\mathcal X_{\TT}=C^\infty_{\mathrm{div}}(\TT;\R^3)`
>
> `02-preliminaries.tex:10`:
> `\FF=\mathcal F_{\TT}=C_c^\infty(\TT\times(0,\infty);\R^3)`
>
> `02-preliminaries.tex:23-26`: “Thus periodic forces vanish near zero and
> outside a compact time interval ... Both classes consist of forces defined
> through any possible singular time of the velocity.”

Therefore `initialClassT` has smoothness, periodicity, and zero divergence but
no mean-zero condition.  For the periodic lift of `𝓕_𝕋`, compact support on
`𝕋³ × (0,∞)` becomes compact support in positive time only; imposing compact
spatial support on the lift to `ℝ³` would force it to vanish.  Both drafts read
`𝒳_𝕋` this way.  A described the force as vanishing outside a compact positive
time set; B used the equivalent support inclusion
`tsupport f ⊆ K ×ˢ univ`.  The reconciliation keeps B's `MemForceT` spelling.

## Paper clause → Lean declaration, provenance, and ruling

| Paper clause / notion | Reconciled Lean declaration | Draft A | Draft B | Reconciliation ruling |
|---|---|---|---|---|
| Unit torus and lattice (`03-torus.tex:1-4`) | `PeriodicTorus`, `PeriodicFrequency`, `periodicTorusMeasure` | `UnitAddTorus (Fin 3)`, `Fin 3 → ℤ`; vector-inside-`lp` arrangement | Same torus/lattice; normalized Haar made explicit | Keep B, including the probability Haar measure. |
| Physical representation (P) (`02-preliminaries.tex:28`) | `IsPeriodicSpatial`, `IsPeriodicOn` | Quantified every lattice translate `k : Fin 3 → ℤ` | Quantifies positive unit shifts coordinatewise, with all `x`; negative/integer shifts follow | Keep B's names and shape. API fields `torusLift_injective`/`torusLift_surjective` state the two directions of the quotient bridge. |
| Canonical torus realization and Fourier coefficient (`01-introduction.tex:83-90`) | `torusLift`, `periodicFourierCoeff` | Expanded `torusRepresentative`; vector coefficient bundled as `periodicFourierCoeffT` | Restates `Paper1/TorusCube.lean`'s representative and scalar coefficient directly | Keep B. Future binding proves equality with the local definitions. |
| Real coefficient carrier (`01-introduction.tex:83-103`; `02-preliminaries.tex:72-73`) | `PeriodicScalarData`, `PeriodicVectorData`, `realPeriodicSubmodule`, `PeriodicSobolev s` | Raw `lp` of complex Euclidean vectors; reality only in `IsPeriodicDatum` | `WithLp 2` of three scalar `lp` sequences, restricted to `A_i(-k)=conj(A_i(k))` | Keep B: all quantified data belong to the real Hilbert carrier. `TorusDataAPI.datum_real` exposes the symmetry. |
| Inhomogeneous weight (`01-introduction.tex:83-84`) | `periodicFrequencyWeight` | Split squared frequency and `periodicSobolevWeight` | `1 + 4π²∑ k_i²`, raised to `s/2` in the datum relation | Keep B's exact unit-period normalization. |
| Physical field ↔ weighted datum (`01-introduction.tex:83-103`) | `IsPeriodicDatum` | Periodicity, explicit integrability, frequency-first vector equality, explicit reality | Periodicity followed by exact order `∀ i, ∀ k`; realness lives in the carrier | Keep B. Datum uniqueness and existence/Parseval directions are API facts, not definition conjuncts. |
| Physical `H^s(𝕋³)` norm (`01-introduction.tex:83-103`) | `periodicSobolevENorm` | Infimum over raw represented data | Infimum over represented real data | Keep B; empty infimum is `⊤`. |
| Homogeneous convention (`01-introduction.tex:105-109`) | `periodicAngularFrequencySq`, `homogeneousDatumWeight`, `IsPeriodicHomogeneousDatum`, `periodicHomogeneousENorm` | Absent | Absent | Add from T12 Draft A's shape: weight `|2πk|^s`, explicit zero branch forcing `A(0)=0`, and the paper's required mean-zero physical realization. |
| Spatial mean and splitting (`03-torus.tex:395-411`) | `meanT`, `constantPartT`, `meanZeroPartT`, `meanDecompositionT`, `IsMeanZeroT` | Componentwise Haar mean; `meanPartT`; coefficient mode operations | Vector Bochner integral; named physical decomposition | Keep B's names. `TorusDataAPI.mean_decomposition` and `meanZero_datum` register the reconstruction and zero-mode facts. |
| Mean-zero coefficient space (`01-introduction.tex:105-109`) | `meanZeroPeriodicSobolev s` | Complex submodule with bundled-vector zero mode | Real submodule with `∀ i, A_i(0)=0` | Keep B, matching the chosen real carrier. |
| Solenoidality and Leray (`02-preliminaries.tex:76-80`) | `IsSolenoidalPeriodicDatum`, `periodicLeray`, `IsPeriodicLerayDatum` | Geometric orthogonal projector as a total map; predicate named `IsSolenoidalDatum` | Exact coordinate symbol plus graph relation in the real carrier | Keep B's names and graph. The API registers existence, contraction, idempotence, fixed points, weight commutation, and zero-mode preservation. |
| Force paths and norms (`01-introduction.tex:118-140`; `03-torus.tex:7`) | `IsPeriodicSobolevPath`, `forceSobolevENormT` | All `t ≥ 0`, strongly measurable path, separate datum norm helper | Same quantifiers with `eLpNorm` inline | Keep B. No `.toReal` totalization. |
| Initial class `𝒳_𝕋` (`02-preliminaries.tex:9`) | `initialClassT` | Smooth + periodic + divergence-free; no mean-zero condition | Same | Paper decides in favor of the shared reading: nonzero spatial means are allowed. |
| Force class `𝓕_𝕋` (`02-preliminaries.tex:10,23-26`) | `MemForceT`, `forceClassT` | Compact positive time set; zero outside it | `tsupport f ⊆ K ×ˢ univ`, `K` compact and `K ⊆ Ioi 0` | Keep B. This is compact time support of the periodic lift, not spatial compactness in `ℝ³`. |
| Pressure normalization (`02-preliminaries.tex:28,84-88`; `03-torus.tex:319`) | `pressureMeanT`, `PressureGaugeT`, `normalizePressureT` | `HasZeroPressureMeanT`, with explicit integrability | `PressureGaugeT` | Keep B's name; add the normalization function needed by the API preservation field. |
| Classical periodic solution (`02-preliminaries.tex:28-36,101-114`) | `ClassicalSolutionT` | New structure with torus-specific fields interspersed; no `pressure_gradient` | New structure; common fields nearly mirror `ClassicalSolutionR`, gauge last; no `pressure_gradient` | Mirror `Data.ClassicalSolutionR` exactly through `pressure_gradient`: `velocity`, `pressure`, `horizon_pos`, `velocity_smooth`, `pressure_smooth`, `initial`, `divergence`, `momentum`, `sobolev`, `pressure_gradient`; append only `velocity_periodic`, `pressure_periodic`, `pressure_gauge`. The gradient is measured on Haar `𝕋³`, not the infinite periodic lift. |
| Maximal lifespan / regular through `T` (`02-preliminaries.tex:32-36`) | `maximalLifespanT`, `RegularThroughT` | Both definitions; A also named the zero-data breakdown specialization | Same definitions | Keep B's definitions and names. |
| Breakdown set (`02-preliminaries.tex:38-48`) | `breakdownSetInT`, `breakdownSetT` | Fixed `forceClassT` only | Parametric ambient class followed by the `forceClassT` specialization | Keep B, matching `Data.breakdownSetIn`. |
| Relative density (`03-torus.tex:6-15,350-355`) | `RelativelyDenseT` | Parametric `Y,S`, exact approximation order | Same | Keep B's spelling, matching `Data.RelativelyDense`. This is generic in `q`; T10 states no density theorem or critical-threshold theorem. |
| Energy norm (`01-introduction.tex:143-150`; `03-torus.tex:299,540-561`) | `energyEssSupT`, `energyGradientT`, `energyENormT`; coefficient spellings | Coefficient-side order-zero plus homogeneous gradient expression | Physical Haar `L∞_tL²_x + L²_tL²_x` gradient expression | Keep B's split and name `energyENormT`; add `coefficientEnergyENormT` and `TorusDataAPI.energy_eq_physical` to register the Parseval equivalence. |
| Consumer-facing facts selected by the lead | `TorusDataAPI` | Facts appeared only in the “Needs a lemma” list | Facts appeared only in the “Needs a lemma” list | Register concrete fields for uniqueness/reality, Parseval and quotient bridges, mean identities, Leray properties, pressure normalization, energy equivalence, and classical-solution transports. Every field records exact binder order and a non-vacuity explanation. |

## Registered-vocabulary checks

The lane brief requested the two whole-space abbreviation checks even though no
T10 definition uses completed density.  `Spec.lean` contains literal generic
checks accepted by Lean:

```lean
example ... : CompletedDense q s S =
    CompletedDenseVia q s (IsSobolevPath s) S := rfl
example ... : CompletedDenseHomogeneous q s S =
    CompletedDenseVia q s (IsHomogeneousPath s) S := rfl
```

The brief's `q : ℝ≥0∞`, `(q = 1 ∨ q = 2)`, and
`criticalOrder q.toReal` prescription belongs to theorem APIs such as R46.
The T10 reconciliation selects only generic data-layer definitions and facts;
there is no threshold-bearing T10 field in which to insert those binders.
`RelativelyDenseT` therefore remains correctly generic in `q`, exactly as both
T10 drafts and the lead's decision require.

## Proof dependencies

The lead's reconciliation states the dependency surface verbatim as follows:

> “the registered contract's fields are the basic facts every consumer needs:
> datum uniqueness, `IsPeriodicDatum` real, Parseval/`TorusCube` bridge both
> ways, mean decomposition identities, Leray is a contraction/projector
> commuting with the weight, mean-zero preservation, pressure gauge preserves
> the equation, `energyENormT` ≡ physical energy norm, the
> `ClassicalSolutionR`-style transports”.

These are the fields of `TorusDataAPI`.  Their analytic and local-interface
sublemmas are itemized below; those items are T10's later proof lanes.

## Needs a lemma

This is the union of both blind drafts' lists, with duplicate statements merged
but no obligation dropped.

1. Identify `torusLift` and `periodicFourierCoeff` with
   `NSFormalization.Paper1.TorusCube`; prove lift measurability/continuity for
   continuous periodic fields, and identify Haar integration with integration
   over the unit cube.
2. Prove scalar and vector Parseval/Plancherel, including equality of the
   order-zero datum norm with physical `L²(𝕋³)` and the full-gradient identity
   with the exact `2πk` factors.
3. Prove positivity and evenness of `periodicFrequencyWeight`, equality with
   the local periodic weight, `IsPeriodicDatum` uniqueness/injectivity, and
   existence at every required real order for smooth periodic fields.
4. Prove Fourier reality for real periodic physical fields and preservation of
   conjugate-reflection symmetry by subtraction, scalar weights, derivatives,
   Leray, and the other multipliers used downstream.
5. Prove that the zero coefficient is `meanT`; prove reconstruction,
   zero-mean of `meanZeroPartT`, orthogonality of the two modes, the corresponding
   coefficient decomposition, and that deleting the zero mode cannot increase
   any `H^s` norm.
6. Prove the coordinate formula for the geometric Leray symbol used by local
   code: identity at `k=0` and
   `v_i-k_i(∑_j k_jv_j)/|k|²` for `k ≠ 0`.
7. Prove that B's coordinate Leray formula defines an element of
   `PeriodicSobolev s`; prove linearity, self-adjointness, idempotence,
   contraction, preservation of reality and the zero mode, solenoidal range,
   and that every solenoidal datum is fixed.
8. Prove Leray commutes with Bessel/homogeneous scalar weights, derivatives,
   `Λ`, and the periodic heat multiplier.
9. Prove equivalence, for smooth represented fields, between pointwise physical
   divergence-free and `IsSolenoidalPeriodicDatum`, in both directions.
10. Prove pressure normalization preserves periodicity, smoothness, spatial
    gradient, and the momentum equation; produces `PressureGaugeT`; and gives
    the unique zero-mean periodic representative.
11. Prove smooth compact-time-supported periodic forces admit smooth,
    continuous/strongly measurable coefficient paths at every integer order,
    have finite `L¹_tH^m_x` and `L²_tH^m_x` norms, and identify `MemForceT` with
    the existing `PeriodicForceSpace` interface.
    Registered/proved by lane 312: `ForcePaths.lean` exports `force_coefficient_path`
    in the T10 namespace, which supplies continuous, strongly measurable compactly supported
    paths with the amended datum at every time and every integer order;
    `forceSobolevENormT_ne_top` covers every exponent, including 1 and 2.
    `memForceT_iff_isTestForce` identifies the Paper1 interface. Smoothness
    of the coefficient-valued path itself is not asserted.
12. Prove the physical/coefficient gradient and energy identities and, for
    fixed finite `T`, equivalence of `energyENormT` with the usual sum norm on
    `L∞_tL²_x ∩ L²_tH¹_x`.
    Registered/proved by lane 312: `gradientTensor_parseval`,
    `gradient_eq_homogeneousENorm`, and `energyENormT_eq` identify the full
    Frobenius gradient and the physical/coefficient energy, with exact angular
    frequency factors. The energy identity assumes smooth periodic slices on
    `(0,T)` and needs no time regularity. The separate comparison with the
    inhomogeneous intersection sum norm is not claimed by this lane.
13. Prove the mean evolution identity `m'(t)=meanT(f(t))`; derive preservation
    of mean zero for zero-mean forcing and the exact general mean-free equation
    after the Galilean translation used by T11/T20.
14. Prove constant transport by the mean is skew-adjoint in `L²` and commutes
    with every coefficient Sobolev multiplier.
15. Prove spectral gap/Poincaré on `meanZeroPeriodicSobolev`, equivalence of
    homogeneous and inhomogeneous norms there, and Sobolev-order monotonicity.
16. Construct explicit forward/backward fieldwise conversions between
    `ClassicalSolutionT` and the existing local periodic solution/flow
    structure, with both round trips, horizon restriction, and force
    extensionality transports.
17. Use local uniqueness to identify `maximalLifespanT` with the lifespan in the
    existing periodic local theory and prove the breakdown predicate is
    extensional in the force on nonnegative times.

## Lead amendment 1 (2026-09-17)

`IsPeriodicDatum` and `IsPeriodicHomogeneousDatum` now require
`Integrable (torusLift z) periodicTorusMeasure`, and `parseval_forward` carries
`MemLp (torusLift z) 2 periodicTorusMeasure`; see `RECONCILIATION.md` §5 for the
two counterexamples (junk-value Bochner integrals) that forced this.  Proof
lanes must use the amended text.

## Open questions for the owner

1. The paper explicitly says the torus homogeneous norm omits `k=0` and
   requires zero mean (`01-introduction.tex:105-109`).  `Spec.lean` therefore
   puts `IsMeanZeroT z` inside `IsPeriodicHomogeneousDatum`; T12 Draft A kept
   mean zero as a separate hypothesis.  Should the eventual V1 contract keep
   the stronger fail-safe totalization (`⊤` off the mean-zero layer), as here?
2. Draft B, selected by the reconciliation, inherits the totalized
   `UnitAddTorus.mFourierCoeff` without A's explicit integrability conjunct.
   This is harmless on the smooth classes but permits junk coefficients for
   pathological physical functions.  Does the owner want a later V2 physical
   bridge for arbitrary nonsmooth functions, leaving V1 unchanged?
3. The lead asks for `ClassicalSolutionR`-style transports, while the future
   contract cannot import the local periodic flow structure.  The spec exposes
   horizon restriction and force-extensionality as contract fields and leaves
   the local forward/backward conversions in “Needs a lemma”.  Confirm that the
   local conversion theorems should live only in Bindings.
4. The lane brief contains R46-specific residue: citations to
   `04-whole-space.tex`, critical-threshold binders, and completed-density `rfl`
   checks.  The two harmless `rfl` checks are included, but no unrelated
   whole-space density theorem was added to T10.  Confirm those other clauses
   should be removed when the task template is next reused.
5. A literal reading of “one structure” conflicts with the binding decision to
   have both the vocabulary record `ClassicalSolutionT` and the fact record
   `TorusDataAPI`.  The spec follows the mathematical reconciliation and keeps
   exactly those two structures.  Confirm this is the intended contract shape.

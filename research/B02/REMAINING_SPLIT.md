# B02 remaining-fields split (lane 097)

Input for the `B02` contract lane.  The seven merged `B02` modules
(`LowFrequency`, `Annular`, `LowHigh`, `Cutoff`, `LebesgueDatum`,
`AnnularSchwartz`, `AnnularReal`) already discharge **11** fields of
`research/B02/Spec.lean`'s `HomogeneousApproxAPI`; this table is the **8**
that were not, split into `S` (direct reuse, proved this lane) and `M`
(needs a new lemma, documented not forced).

## Already discharged by the seven modules (context, not this lane's work)

| field | Spec:line | theorem (file:line) |
|---|---|---|
| `annularRestriction` | :302 | `Section4/B02/Annular.lean:240` |
| `annularSmoothing` | :314 | `Section4/B02/Annular.lean:337` |
| `annularSchwartz` | :362 | `Section4/B02/AnnularReal.lean:205` |
| `lowFrequencyIntegrable` | :370 | `Section4/B02/LowFrequency.lean:56` |
| `lowFrequencyIntegral` | :378 | `Section4/B02/LowFrequency.lean:67` |
| `fourierSupBound` | :397 | `Section4/B02/LowFrequency.lean:124` |
| `lowHighSplit` | :421 | `Section4/B02/LowHigh.lean:200` |
| `lebesgueHomogeneousDatum` | :454 | `Section4/B02/LebesgueDatum.lean:405` |
| `homogeneousDatumSub` (integrability-carrying form) | :490 | `Section4/B02/LebesgueDatum.lean:446` (`isHomogeneousSliceDatum_sub_of_integrable`) |
| `cutoffLebesgue` | :513 | `Section4/B02/Cutoff.lean:225` |
| `spatialApproxHomogeneous` | :539 | `Section4/B02/AnnularReal.lean:225` (unconditional) |

## Remaining fields — the 8 rows

Legend: `S` = discharged this lane by a direct reuse; `M` = needs a new lemma.

### `S` rows — proved in `Section4/B02/Remaining.lean` this lane

| # | field | Spec:line | exact Spec statement (after `open Set … Data`) | size | inputs (file:line) | how discharged |
|---|---|---|---|---|---|---|
| 1 | `chi_smooth` | :280 | `ContDiff ℝ ∞ χ` | S | vendor `baseCutoff_smooth` (`ComparisonCutoffs.lean:40`) | `χ := baseCutoff`; `Remaining.lean:chi_smooth` |
| 2 | `chi_one` | :282 | `∀ x : Space, ‖x‖ ≤ 1 → χ x = 1` | S | vendor `baseCutoff_eq_one` (`:46`) | `Remaining.lean:chi_one` |
| 3 | `chi_vanishes` | :285 | `∀ x : Space, 2 ≤ ‖x‖ → χ x = 0` | S | vendor `baseCutoff_eq_zero` (`:50`) | `Remaining.lean:chi_vanishes` |
| 4 | `chi_range` | :287 | `∀ x : Space, χ x ∈ Icc (0:ℝ) 1` | S | vendor `baseCutoff_nonneg`/`_le_one` (`:42,44`) | `Remaining.lean:chi_range` |
| 5 | `temporalApprox` | :563 | `∀ q, 1≤q → q≠⊤ → ∀ s b, MemBochnerDatum q s b → ∀ η, 0<η → ∃ J φ A, (smooth) ∧ (compact) ∧ (supp⊆Ioi 0) ∧ bochnerDatumENorm q s (separatedPath φ A - b) < η` | S | `Section4/B01/Temporal.lean:170` `temporalApprox` | token-identical to the registered `B01` field (`Contracts/V1/BochnerPartial.lean:132-138`); `Remaining.lean:temporalApprox := B01.temporalApprox` |

**Notes on the `S` rows.**

* `chi_*` — the same binding the `B01` contract uses
  (`Bindings/BochnerPartial.lean:66-71`).  `χ := NavierStokesR3.ComparisonCutoffs.baseCutoff`.
* `temporalApprox` — checked **token-identical** to `Contracts/V1/BochnerPartial.lean:132-138`
  (character-for-character; diff below).  The manuscript states the Bochner step
  "for any of the preceding separable Hilbert spaces" (`04-whole-space.tex:251`)
  and it lives on the datum carrier `RealVectorSobolev s`, which is the *same*
  carrier the homogeneous realization reads (`Data.lean:367-378`).  The only
  textual difference is the spec-local `separatedPath` namespace
  (`BlowupDensity.B02.Draft.separatedPath` vs `…B01…`), and the two `def`s are
  identical (`fun t => ∑ j, φ j t • A j`), hence definitionally equal.  So it is a
  **direct reuse**, not a homogeneous variant.

### `M` rows — not proved this lane (documented, not forced)

| # | field | Spec:line | size | needed lemma / route | blocker |
|---|---|---|---|---|---|
| 6 | `separatedAssembly` | :582 | M (~80-120 ln) | homogeneous datum-path additivity `isHomogeneousPath_separated` (below) | no scalar-`smul`/finite-`sum` combinator for `IsHomogeneousSliceDatum` exists — only `isHomogeneousSliceDatum_sub` (`HomogeneousWitness.lean:585`) |
| 7 | `annularPathApprox` | :337 | M (~100-150 ln) | path-level annular truncation via measurable selection + DCT (below) | no measurable-in-`t` selection of `annularTruncLp δ R (b t)` and no path-level DCT over `(δ,R)` |
| 8 | `approxCompactHomogeneous` | :607 | M-L (largest) | `SeparatedCompactHomogeneousDense` glue: `temporalApprox` + `spatialApproxHomogeneous` + `separatedAssembly` (below) | depends on row 6; and `B01`'s `approxCompact` is **monolithic** (not this glue), so cannot be reused/parametrized |

**Row 6 — `separatedAssembly` (Spec:582).**
Exact statement conclusion:
`MemForceCompact (separatedField φ h) ∧ IsHomogeneousPath s (separatedField φ h) (separatedPath φ A) ∧ AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure`,
hypotheses `(∀ j, ContDiff ∞ φ j)`, `(∀ j, HasCompactSupport φ j)`,
`(∀ j, tsupport φ j ⊆ Ioi 0)`, `(∀ j, ContDiff ∞ h j)`, `(∀ j, HasCompactSupport h j)`,
`(∀ j, IsHomogeneousSliceDatum s (h j) (A j))`.
Differs from `B01`'s (`Contracts/V1/BochnerPartial.lean:145-153`) in **exactly one
conjunct and its matching hypothesis**: `IsHomogeneousPath`/`IsHomogeneousSliceDatum`
replace `IsSobolevPath`/`IsSobolevDatum`.
* conjunct 1 (`MemForceCompact`) and conjunct 3 (`AEStronglyMeasurable`) are
  realization-independent, **identical** to `B01`, dischargeable by
  `Section4/B01/Separated.lean`'s `memForceCompact_of_smooth_support ∘ {contDiff,hasCompactSupport,tsupport_…}_separatedField` and `aestronglyMeasurable_separatedPath` (`:220-233,207`).
* conjunct 2 is the new lemma, the homogeneous twin of
  `Section4/B01/Separated.lean:182` `isSobolevPath_separated`:
  `isHomogeneousPath_separated : (∀ j, Continuous (h j)) → (∀ j, HasCompactSupport (h j)) → (∀ j, IsHomogeneousSliceDatum s (h j) (A j)) → IsHomogeneousPath s (separatedField φ h) (separatedPath φ A)`.
  Route: for each `t ≥ 0` the slice `x ↦ ∑ j φ j t • h j x` carries `∑ j φ j t • A j`.
  `B01`'s path lemma is *free additivity* — `IsSobolevDatum` is defined through the
  bundled ℂ-CLM `angularRealization`, so `map_sum`/`map_smul` do it (`Separated.lean:104-110`).
  `IsHomogeneousSliceDatum` is `∃ U, IsSliceDistribution z U ∧ IsHomogeneousVectorDatum s U G`
  and the additivity carries **integrability side conditions** (the totalization
  caveat that refuted the hypothesis-free `homogeneousDatumSub`,
  `REVIEW_U6.md` §4).  Those side conditions ARE dischargeable here because each
  `h j` is smooth compact (`Section4/B01/Separated.lean:73` `integrable_schwartz_mul`
  pattern).  The missing pieces: a scalar-`smul` and finite-`sum` combinator for
  `IsHomogeneousDatum`/`IsHomogeneousVectorDatum`/`IsSliceDistribution`
  (generalising `HomogeneousWitness.lean:534-594`'s `_sub` lemmas from "difference of
  two" to "`ℝ`-combination of `Fin J`"), plus the `coe_sum_smul_apply` /
  `space_sum_apply` bookkeeping already in `Separated.lean:90-102`.

**Row 7 — `annularPathApprox` (Spec:337).**
Exact statement:
`∀ q, 1≤q → q≠⊤ → ∀ s b, MemBochnerDatum q s b → ∀ η, 0<η → ∃ δ R D, 0<δ ∧ δ<R ∧ (∀ t, IsAnnularRestriction δ R (b t) (D t)) ∧ MemBochnerDatum q s D ∧ bochnerDatumENorm q s (D - b) < η`.
Not a step of the manuscript's own proof (which does the Bochner reduction first,
`04-whole-space.tex:251`, then truncates the finitely many fibre values); recorded
as the path-first shape.  Route through `Section4/B02/Annular.lean`: the slice-level
`annularTruncLp δ R` (`:205`), `annularTruncLp_ae`/`_mem` (`:210,217`), the fibre
approximation `annularRestriction` (`:240`), and `tendsto_eLpNorm_annulus_compl`
(`:151`).  A single `(δ,R)` suffices for the whole path (the truncation is an
`indicator` contraction on each fibre), pushed by dominated convergence.
Blocker: (a) measurability of `t ↦ annularTruncLp δ R (b t)` giving `MemBochnerDatum q s D`,
and (b) the path-level DCT/monotone-in-`(δ,R)` argument sending
`bochnerDatumENorm q s (D - b) → 0` — neither exists.  Self-contained M.

**Row 8 — `approxCompactHomogeneous` (Spec:607).**
Exact statement: `∀ q, 1≤q → q≠⊤ → ∀ s, SplitRange s → CompletedDenseHomogeneous q s forceClassCompact`.
**Key finding:** `B01`'s `approxCompact` (`Section4/B01/Compact.lean:155`) is
**monolithic** — it applies the source density theorem
`Paper3.exists_angular_real_vector_positive_physical_approx` (which emits an
`IsSobolevPath` directly) and does **not** glue `temporalApprox` + `spatialApprox` +
`separatedAssembly`.  There is no homogeneous analogue of that source theorem, so
`approxCompactHomogeneous` **cannot** reuse `B01`'s proof, parametrized or copied.
It must be assembled fresh through the `SeparatedCompactHomogeneousDense` route
(`Spec.lean:640-664`): `temporalApprox` (row 5, done) → separated sum with
coefficients `A' j` within `η/2`; `spatialApproxHomogeneous` (done) → replace each
`A' j` by the datum `A j` of a physical `h j ∈ C_c^∞(R³;R³)`, controlling the summed
replacement error; `separatedAssembly` (row 6, M) → the sum lies in `F_c` with
`IsHomogeneousPath`; then the `CompletedDenseVia` conclusion.  Blocker: depends on
row 6, plus the new triangle-inequality glue bounding
`bochnerDatumENorm q s (separatedPath φ A' - separatedPath φ A)` by the weighted sum
of the fibre errors `‖A' j - A j‖ₑ`.  Largest remaining field (M-L).

## The registered-shape check for `temporalApprox`

`B02` `Spec.lean:563-573` vs `B01` `Contracts/V1/BochnerPartial.lean:132-138`:
identical modulo `separatedPath`'s namespace.  Both read

```
∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ (s : ℝ)
    (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b → ∀ η : ℝ≥0∞, 0 < η →
  ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
    (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
    (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
    bochnerDatumENorm q s (separatedPath φ A - b) < η
```

so the `B02` contract binding can point `temporalApprox` at
`NSFormalization.Section4.B01.temporalApprox` (or the re-export
`NSFormalization.Section4.B02.temporalApprox`) exactly as `Bindings/BochnerPartial.lean:73`
does.

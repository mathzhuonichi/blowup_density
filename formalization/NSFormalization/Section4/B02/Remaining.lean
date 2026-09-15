import NSFormalization.Section4.B01.Temporal
import NavierStokes.R3.ComparisonCutoffs

/-!
# B02 remaining fields (lane 097): the `S`-size fields of `HomogeneousApproxAPI`

The seven merged `B02` modules (`LowFrequency`, `Annular`, `LowHigh`, `Cutoff`,
`LebesgueDatum`, `AnnularSchwartz`, `AnnularReal`) discharge the homogeneous
spatial clause + cutoff + diagonal of Proposition 4.6's `L²(0,∞;Ḣ^{-1})` clause
(`paper/sections/04-whole-space.tex:218-260`): the fields `annularRestriction`,
`annularSmoothing`, `annularSchwartz`, `lowFrequencyIntegrable`,
`lowFrequencyIntegral`, `fourierSupBound`, `lowHighSplit`,
`lebesgueHomogeneousDatum`, `homogeneousDatumSub` (integrability-carrying form,
`isHomogeneousSliceDatum_sub_of_integrable`), `cutoffLebesgue` and
`spatialApproxHomogeneous` of `research/B02/Spec.lean`'s `HomogeneousApproxAPI`.

This module discharges the remaining **`S`-size** fields — the ones proved by a
direct reuse of an existing declaration, exactly as the `B01` contract binding
(`verification/Bindings/BochnerPartial.lean:66-73`) discharges the same shapes:

* `chi_smooth`, `chi_one`, `chi_vanishes`, `chi_range` — the fixed spatial cutoff
  `χ` of `04-whole-space.tex:235`, reused at `:249`.  `χ := baseCutoff` and its
  four properties are the vendor `NavierStokesR3.ComparisonCutoffs.baseCutoff`
  estimates verbatim, the identical binding `B01` uses.
* `temporalApprox` — the Bochner stage `04-whole-space.tex:251-260`.  The `B02`
  field is **token-identical** to the registered `B01` field
  (`verification/Contracts/V1/BochnerPartial.lean:132-138`); it is stated "for
  any of the preceding separable Hilbert spaces" and lives on the datum carrier,
  not on a realization, so `NSFormalization.Section4.B01.temporalApprox`
  discharges it verbatim (the only difference is the spec-local `separatedPath`
  namespace, and the two `separatedPath` `def`s are definitionally equal).

The `M`-size fields — `separatedAssembly` (needs the homogeneous datum-path
additivity of a finite separated sum, `IsHomogeneousPath` in place of `B01`'s
`IsSobolevPath`), `annularPathApprox` (the path-level annular truncation) and
`approxCompactHomogeneous` (the final temporal + spatial diagonal gluing) — are
**not** discharged here; see `research/B02/REMAINING_SPLIT.md` and
`research/B02/ATTEMPTS_REMAINING.md` for the precise lemma each needs and its
size.

## Restated `Contracts.V1.Data` vocabulary

`formalization/` is an upstream Lake package of `verification/` and cannot import
`Contracts.*`.  `MemBochnerDatum`, `bochnerDatumENorm` and `separatedPath` in the
`temporalApprox` field below are reused from `Section4/B01/{Compact,Separated}.lean`,
which restate them token-for-token from `Contracts/V1/Data.lean:212,205` and
`research/B01/Spec.lean:147`; `χ`'s type `Space → ℝ` needs no restatement.  The
conformance file `research/B02/axioms_remaining.lean` discharges each spec field
through the resulting definitional equalities.
-/

noncomputable section

namespace NSFormalization.Section4.B02

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokesR3.ComparisonCutoffs
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. The fixed spatial cutoff `χ` (`04-whole-space.tex:235`, reused at `:249`) -/

/-- `research/B02/Spec.lean:279` `chi_smooth`: `χ` is smooth, `04-whole-space.tex:235`.
Discharged by the vendor `baseCutoff_smooth`, `χ := baseCutoff`, exactly as the
`B01` binding (`Bindings/BochnerPartial.lean:67`). -/
theorem chi_smooth : ContDiff ℝ ∞ (baseCutoff : Space → ℝ) :=
  baseCutoff_smooth

/-- `research/B02/Spec.lean:281` `chi_one`: `χ = 1` on the closed unit ball,
`04-whole-space.tex:235`.  Vendor `baseCutoff_eq_one`, `B01`'s binding at `:68`. -/
theorem chi_one : ∀ x : Space, ‖x‖ ≤ 1 → baseCutoff x = 1 :=
  fun _ hx => baseCutoff_eq_one hx

/-- `research/B02/Spec.lean:285` `chi_vanishes`: `χ = 0` outside the ball of
radius two, `04-whole-space.tex:235`.  Vendor `baseCutoff_eq_zero`, `B01`'s
binding at `:69`. -/
theorem chi_vanishes : ∀ x : Space, 2 ≤ ‖x‖ → baseCutoff x = 0 :=
  fun _ hx => baseCutoff_eq_zero hx

/-- `research/B02/Spec.lean:287` `chi_range`: `0 ≤ χ ≤ 1`, `04-whole-space.tex:235`.
Vendor `baseCutoff_nonneg`/`baseCutoff_le_one`, `B01`'s binding at `:70-71`. -/
theorem chi_range : ∀ x : Space, baseCutoff x ∈ Icc (0 : ℝ) 1 :=
  fun x => ⟨baseCutoff_nonneg x, baseCutoff_le_one x⟩

/-! ## 2. The Bochner temporal stage (`04-whole-space.tex:251-260`, shared with `B01`) -/

/-- `research/B02/Spec.lean:563` `temporalApprox`.  Finite separated sums with
`C_c^∞((0,∞))` time factors are dense in the datum-path Bochner space
`L^q(0,∞;Ḣ^s)`, for every real `s` and every `q ∈ [1,∞)`.

The `B02` field is the registered `B01` field verbatim
(`Contracts/V1/BochnerPartial.lean:132-138`): `04-whole-space.tex:251` states the
Bochner step "for any of the preceding separable Hilbert spaces", and it lives on
the datum carrier `RealVectorSobolev s`, which is the *same* carrier the
homogeneous realization reads (`Data.lean:367-378`), so no homogeneous variant is
needed.  Discharged by `NSFormalization.Section4.B01.temporalApprox`, whose
statement uses `Section4/B01/{Separated,Compact}.lean`'s `separatedPath`,
`MemBochnerDatum` and `bochnerDatumENorm` — the same objects `B02`'s field names
through the `Contracts.V1.Data` defeq. -/
theorem temporalApprox : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ (s : ℝ)
    (b : ℝ → RealVectorSobolev s), NSFormalization.Section4.B01.MemBochnerDatum q s b →
    ∀ η : ℝ≥0∞, 0 < η →
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      NSFormalization.Section4.B01.bochnerDatumENorm q s
        (NSFormalization.Section4.B01.separatedPath φ A - b) < η :=
  NSFormalization.Section4.B01.temporalApprox

end NSFormalization.Section4.B02

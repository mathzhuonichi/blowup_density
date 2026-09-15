import NSFormalization.Section4.B01.Compact
import NSFormalization.Section4.B01.Separated
import NSFormalization.Paper3.PositiveTemporalDensity

/-!
# B01 unit 7: the real positive-time Bochner temporal approximation

This module discharges the `B01` obligation `temporalApprox` of `research/B01/Spec.lean:273`
(unit 7 of `research/B01/COMPARISON.md:151`) and the standalone predicate
`SeparatedTemporalDense` (`research/B01/Spec.lean:382`).  It is the Lean form of the Bochner stage
of Proposition 4.6, `paper/sections/04-whole-space.tex:251-260`: finite separated sums
`Σ_{j<J} φ_j(t) • A_j`, with smooth compactly supported time factors `φ_j` supported strictly in
`(0,∞)` and arbitrary spatial data `A_j ∈ H^s(R³;R³)`, are dense in the datum-path Bochner space
`L^q(0,∞;H^s)` for every real `s` and every `q ∈ [1,∞)`.

## Route (`research/B01/COMPARISON.md:151`, row 7)

1. `Paper3.dense_span_separatedLp` (`SeparatedBochnerDensity.lean:30`) at
   `H := RealVectorSobolev s`, `μ := forceTimeMeasure`, coefficient set `univ`, scalar time set
   `Paper3.dense_positive_temporal_factors` (`PositiveTemporalDensity.lean:73`): the finite
   separated span of `separatedLp q h g` with `g` a positive-time `C_c^∞` factor is dense in
   `Lp (RealVectorSobolev s) q forceTimeMeasure`.
2. `Submodule.mem_span_set'` unwraps a span element into a *finite* `Fin n`-indexed `ℝ`-linear
   combination `Σ_i f i • separatedLp q (h i) (g i)`.  A scalar multiple `f i • (g i)` of a
   positive-time factor is again a smooth compactly supported factor supported in `(0,∞)`, so the
   combination has exactly the separated shape `separatedPath φ A` with `φ i := f i • a i`,
   `A i := h i` (`separatedLp_ae`).
3. `Lp.coeFn_*` + `eLpNorm_congr_ae` + `Lp.enorm_def` move from the `Lp` quotient to the raw
   `bochnerDatumENorm` on representatives; the `ENNReal.ofReal`/`toReal` bookkeeping (with the
   `η = ⊤` case) turns the metric `dist B y < ε` into `bochnerDatumENorm … < η`.

## Restated `Contracts.V1.Data` vocabulary

`formalization/` is an upstream Lake package of `verification/` and cannot import `Contracts.*`.
`separatedPath` is reused from `Section4/B01/Separated.lean` (restated verbatim from
`research/B01/Spec.lean:147`); `MemBochnerDatum`, `bochnerDatumENorm` and `forceTimeMeasure` from
`Section4/B01/Compact.lean` / `Section4/D01/ForceClass.lean` (token-for-token with
`Contracts/V1/Data.lean:212,205,118`).  The conformance file `research/B01/axioms_u7.lean`
discharges the spec field and the spec `def` through the resulting definitional equalities.
-/

noncomputable section

namespace NSFormalization.Section4.B01

open Set MeasureTheory
open NSFormalization.Paper3
open NSFormalization.Section4.D01
open scoped ContDiff ENNReal

/-! ## 0. A finite-`Lp`-sum coefficient lemma -/

/-- The coefficient function of a finite `Lp` sum is, almost everywhere, the pointwise finite sum
of the summands' coefficient functions.  Mathlib has `lp.coeFn_sum` for the sequence space but no
`Lp.coeFn_sum`; this is the `Lp`-quotient version, by induction on the finite index set. -/
theorem lp_coeFn_finsetSum {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {μ : Measure ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {ι : Type*} (t : Finset ι)
    (F : ι → Lp H p μ) :
    (⇑(∑ i ∈ t, F i) : ℝ → H) =ᵐ[μ] fun x => ∑ i ∈ t, (F i : ℝ → H) x := by
  classical
  induction t using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero (E := H) (p := p) (μ := μ)
  | insert a t ha IH =>
      filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ t, F i), IH] with x hadd hIH
      rw [Finset.sum_insert ha, hadd, Pi.add_apply, hIH, Finset.sum_insert ha]

/-! ## 1. Unit 7: the temporal density predicate -/

set_option maxHeartbeats 400000 in
/-- **Unit 7, `SeparatedTemporalDense` / `temporalApprox`** (`research/B01/Spec.lean:382,273`).
Finite separated sums with `C_c^∞((0,∞))` time factors are dense in the datum-path Bochner space
`L^q(0,∞;H^s)`, for every real `s` and every `q ∈ [1,∞)`.  `paper/sections/04-whole-space.tex:251-260`.

The `maxHeartbeats 400000` bump (measured need: 375,034) pays mostly for the final
`bochnerDatumENorm` unfolding over the `RealVectorSobolev` carrier (`hval`, ~50%) and the
per-summand `Lp.coeFn_smul` bookkeeping (`hFi`, ~25%), not for the span-membership step. -/
theorem separatedTemporalDense (q : ℝ≥0∞) (hq1 : 1 ≤ q) (hqt : q ≠ ⊤) (s : ℝ)
    (b : ℝ → RealVectorSobolev s) (hb : MemBochnerDatum q s b) (η : ℝ≥0∞) (hη : 0 < η) :
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      bochnerDatumENorm q s (separatedPath φ A - b) < η := by
  have : Fact (1 ≤ q) := ⟨hq1⟩
  -- The representative of `b` in the completion.
  have hb' : MemLp b q forceTimeMeasure := hb
  set B : Lp (RealVectorSobolev s) q forceTimeMeasure := hb'.toLp b with hBdef
  -- The positive-time temporal factors, retyped at `forceTimeMeasure` so the separated generator
  -- set below is uniform in the measure (avoiding an expensive mixed-measure `whnf`).
  have hdtf : Dense {v : Lp ℝ q forceTimeMeasure | ∃ a : ℝ → ℝ,
      v =ᵐ[forceTimeMeasure] a ∧ HasCompactSupport a ∧ ContDiff ℝ ∞ a ∧
        tsupport a ⊆ Ioi (0 : ℝ)} := dense_positive_temporal_factors q hqt
  -- Density of the separated span (route step 1).
  have hdense := dense_span_separatedLp (H := RealVectorSobolev s) (μ := forceTimeMeasure) q hqt
    (D := Set.univ) dense_univ hdtf
  -- Choose the metric radius `ε`, positive, with `ENNReal.ofReal ε ≤ η`.
  obtain ⟨ε, hεpos, hofle⟩ : ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε ≤ η := by
    by_cases hηtop : η = ⊤
    · exact ⟨1, one_pos, by simp [hηtop]⟩
    · refine ⟨η.toReal, ENNReal.toReal_pos hη.ne' hηtop, ?_⟩
      rw [ENNReal.ofReal_toReal hηtop]
  -- Pick a span element `y` within `ε` of `B`.
  obtain ⟨y, hymem, hdist⟩ := (Metric.mem_closure_iff.mp (hdense B)) ε hεpos
  -- Route step 2: unwrap the span membership into a finite separated combination.
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.mp hymem
  -- Extract, per index, the coefficient `h i`, a smooth representative `a i` of the time factor.
  have key : ∀ i : Fin n, ∃ (h : RealVectorSobolev s) (a : ℝ → ℝ),
      (↑(g i) : Lp (RealVectorSobolev s) q forceTimeMeasure)
          =ᵐ[forceTimeMeasure] (fun t => a t • h) ∧
        HasCompactSupport a ∧ ContDiff ℝ ∞ a ∧ tsupport a ⊆ Ioi (0 : ℝ) := by
    intro i
    -- Reduce the heavy separated-span membership predicate to its existential normal form by a
    -- cheap `simp` rewrite rather than an expensive `whnf` inside `obtain`.
    have hmem := (g i).2
    simp only [Set.mem_ofPred_eq] at hmem
    obtain ⟨hcoef, -, gg, ⟨a, hgae, hac, hsm, hsupp⟩, heq⟩ := hmem
    refine ⟨hcoef, a, ?_, hac, hsm, hsupp⟩
    rw [heq]
    filter_upwards [separatedLp_ae q hcoef gg, hgae] with t ht1 ht2
    rw [ht1, ht2]
  choose hcoef afn hae hac hsm hsupp using key
  -- Assemble the separated data.
  refine ⟨n, fun i => f i • afn i, hcoef, ?_, ?_, ?_, ?_⟩
  · exact fun i => (hsm i).const_smul (f i)
  · exact fun i => show HasCompactSupport ((fun _ : ℝ => f i) • afn i) from (hac i).smul_left
  · exact fun i =>
      show tsupport ((fun _ : ℝ => f i) • afn i) ⊆ Ioi (0 : ℝ) from
        (tsupport_smul_subset_right (fun _ : ℝ => f i) (afn i)).trans (hsupp i)
  -- Route step 3: the norm bound.
  · -- Per-summand a.e. shape.
    have hFi : ∀ i, (⇑(f i • (↑(g i) : Lp (RealVectorSobolev s) q forceTimeMeasure))
        : ℝ → RealVectorSobolev s)
        =ᵐ[forceTimeMeasure] fun t => (f i • afn i) t • hcoef i := by
      intro i
      filter_upwards [Lp.coeFn_smul (f i) (↑(g i) : Lp (RealVectorSobolev s) q forceTimeMeasure),
        hae i] with t ht1 ht2
      rw [ht1, Pi.smul_apply, ht2]
      show f i • (afn i t • hcoef i) = (f i • afn i t) • hcoef i
      rw [smul_smul, smul_eq_mul]
    -- Combine into `⇑y =ᵐ separatedPath φ A`.
    have hyae : (⇑y : ℝ → RealVectorSobolev s) =ᵐ[forceTimeMeasure]
        separatedPath (fun i => f i • afn i) hcoef := by
      rw [← hsum]
      filter_upwards [lp_coeFn_finsetSum Finset.univ
        (fun i => f i • (↑(g i) : Lp (RealVectorSobolev s) q forceTimeMeasure)),
        ae_all_iff.mpr hFi] with t htsum htall
      rw [htsum]
      exact Finset.sum_congr rfl fun i _ => htall i
    -- `b` and its representative agree, phrased on `B`.
    have hBcoe : (⇑B : ℝ → RealVectorSobolev s) =ᵐ[forceTimeMeasure] b := hb'.coeFn_toLp
    -- Difference is a.e. the representative of `y - B`.
    have hdiff : (separatedPath (fun i => f i • afn i) hcoef - b)
        =ᵐ[forceTimeMeasure] (⇑(y - B) : ℝ → RealVectorSobolev s) :=
      (hyae.symm.sub hBcoe.symm).trans (Lp.coeFn_sub y B).symm
    -- Convert to `bochnerDatumENorm` and bound it.
    have hnorm_lt : ‖y - B‖ < ε := by
      rw [← dist_eq_norm, dist_comm]; exact hdist
    have hval : bochnerDatumENorm q s (separatedPath (fun i => f i • afn i) hcoef - b)
        = ‖y - B‖ₑ := by
      show eLpNorm (separatedPath (fun i => f i • afn i) hcoef - b) q forceTimeMeasure = ‖y - B‖ₑ
      rw [eLpNorm_congr_ae hdiff, ← Lp.enorm_def]
    rw [hval, ← ofReal_norm]
    calc ENNReal.ofReal ‖y - B‖ < ENNReal.ofReal ε :=
          (ENNReal.ofReal_lt_ofReal_iff hεpos).mpr hnorm_lt
      _ ≤ η := hofle

/-- **Unit 7, `temporalApprox`** (`research/B01/Spec.lean:273`): the same statement in the exact
shape of the `BochnerApproxAPI` field. -/
theorem temporalApprox : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ (s : ℝ)
    (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b → ∀ η : ℝ≥0∞, 0 < η →
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      bochnerDatumENorm q s (separatedPath φ A - b) < η :=
  fun q hq1 hqt s b hb η hη => separatedTemporalDense q hq1 hqt s b hb η hη

end NSFormalization.Section4.B01

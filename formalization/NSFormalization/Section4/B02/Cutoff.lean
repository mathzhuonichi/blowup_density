import NSFormalization.Section4.B02.Annular
import NSFormalization.Paper3.AngularFourierDilation
import NSFormalization.Source.FourierConvention
import NavierStokes.R3.SchwartzCompactApproximation

/-!
# B02 unit 8: the physical cutoff (`cutoffLebesgue`) and the diagonal assembly

This module discharges the spec field `cutoffLebesgue` of
`research/B02/Spec.lean`'s `HomogeneousApproxAPI` (field at `Spec.lean:489-497`)
and proves the diagonal assembly `spatialApproxHomogeneous` (`Spec.lean:515-518`)
**conditionally** on the exact statements of units 2, 6 and 7
(`annularSchwartz`, `lebesgueHomogeneousDatum` + `homogeneousDatumSub`,
`lowHighSplit`), which are taken as explicit hypotheses of the theorem
`spatialApproxHomogeneous_of`.  The two annular fields it also consumes,
`annularRestriction` and `annularSmoothing`, are the merged unit 1
(`NSFormalization.Section4.B02.Annular`).

The manuscript step is `paper/sections/04-whole-space.tex:249`:

> "Since `(1−χ_R)h_n → 0` in both `L¹` and `L²`, eq:Rnegative-cutoff proves
> `χ_Rh_n → h_n` in `Ḣ^{-1}`.  A diagonal choice gives compact-smooth density in
> this realization, without a dual Sobolev-embedding assumption."

## §0.  Spec predicates restated

`NSFormalization` is a dependency of the `Contracts` library and cannot import
`Contracts.V1.Data`, where the specification lives.  The definitions below are
restated **token-for-token** from `research/B02/Spec.lean` and
`verification/Contracts/V1/Data.lean` (bodies copied verbatim, only the namespace
differs), so that the theorems here are definitionally the spec fields; the
conformance file `research/B02/axioms_u8.lean` discharges the spec-typed
obligations with them.  The scalar cutoff is the vendor bump
`NavierStokesR3.ComparisonCutoffs.baseCutoff`, and
`scaledCutoff baseCutoff R = NavierStokesR3.ComparisonCutoffs.cutoff R` by `rfl`.
-/

noncomputable section

namespace NSFormalization.Section4.B02

open MeasureTheory Set Filter
open NSFormalization.Paper3
open NSFormalization.Source (angularFourier)
open NSFormalization.Source.RealSobolev
open NavierStokes.ProblemStatement (Space)
open NavierStokesR3.ComparisonCutoffs
open NavierStokesR3.SchwartzCompactApproximation
open scoped ENNReal ContDiff Topology BigOperators SchwartzMap

/-- `research/B02/Spec.lean:199`.  The dilated spatial cutoff `χ_R(x) = χ(R⁻¹ • x)`.
With `χ = baseCutoff` this is `NavierStokesR3.ComparisonCutoffs.cutoff R` by `rfl`. -/
def scaledCutoff (χ : Space → ℝ) (R : ℝ) : Space → ℝ := fun x => χ (R⁻¹ • x)

/-- `research/B02/Spec.lean:206`.  The real Euclidean three-vector field assembled
from three real scalar components (`SpatialField = Space → Space`). -/
def schwartzVector (ψ : Fin 3 → SchwartzMap Space ℝ) : Space → Space :=
  fun x => WithLp.toLp 2 (fun i => ψ i x)

theorem scaledCutoff_baseCutoff (R : ℝ) : scaledCutoff baseCutoff R = cutoff R := rfl

@[simp] theorem schwartzVector_apply (ψ : Fin 3 → SchwartzMap Space ℝ) (x : Space) (i : Fin 3) :
    schwartzVector ψ x i = ψ i x := rfl

/-! ## §1.  Elementary vector-norm and regularity facts -/

/-- The Euclidean norm of a three-vector is bounded by the sum of the absolute
values of its components. -/
theorem norm_le_sum_norm (v : Space) : ‖v‖ ≤ ∑ i, ‖v i‖ := by
  rw [PiLp.norm_eq_of_L2]
  have hnn : ∀ i, (0 : ℝ) ≤ ‖v i‖ := fun i => norm_nonneg _
  have hsq : ∑ i, ‖v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 := by
    rw [Fin.sum_univ_three, Fin.sum_univ_three]; nlinarith [hnn 0, hnn 1, hnn 2]
  calc Real.sqrt (∑ i, ‖v i‖ ^ 2)
      ≤ Real.sqrt ((∑ i, ‖v i‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ∑ i, ‖v i‖ := Real.sqrt_sq (Finset.sum_nonneg fun i _ => hnn i)

theorem schwartzVector_contDiff (ψ : Fin 3 → SchwartzMap Space ℝ) :
    ContDiff ℝ ∞ (schwartzVector ψ) :=
  (contDiff_piLp 2).mpr (fun i => (ψ i).smooth')

theorem schwartzVector_memLp (ψ : Fin 3 → SchwartzMap Space ℝ) (p : ℝ≥0∞) :
    MemLp (schwartzVector ψ) p volume :=
  memLp_piLp_iff.mpr (fun i => (ψ i).memLp p volume)

/-! ## §2.  The scalar cutoff error tends to zero in `Lᵖ` -/

/-- For a complex Schwartz function `g`, the `Lᵖ` norm of the cutoff complement
`(1 − χ_R) g` tends to zero as `R → ∞`.  Built from the vendor Schwartz-seminorm
estimate `seminorm_truncate_sub_le` and the continuity of `SchwartzMap.toLpCLM`. -/
theorem tendsto_eLpNorm_cutoff_compl (g : SchwartzMap Space ℂ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Tendsto (fun R : ℝ => eLpNorm (fun x => (1 - cutoff R x) • g x) p volume)
      atTop (𝓝 0) := by
  classical
  set L := SchwartzMap.toLpCLM ℂ ℂ p (volume : Measure Space) with hL
  set S : ℝ → SchwartzMap Space ℂ :=
    fun R => truncate g (max R 1) (lt_of_lt_of_le one_pos (le_max_right R 1)) with hS
  -- Claim A: `S R → g` in the Schwartz topology as `R → ∞`.
  have hSg : Tendsto S atTop (𝓝 g) := by
    rw [(schwartz_withSeminorms ℂ Space ℂ).tendsto_nhds_atTop S g]
    rintro ⟨k, m⟩ ε hε
    refine ⟨max 1 (errorTailBound g k m / ε + 1), fun R hR => ?_⟩
    have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left 1 _) hR
    have hmax : max R 1 = R := max_eq_left hR1
    have hR0 : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
    have hRone : (1 : ℝ) ≤ max R 1 := le_max_right R 1
    have hbound : SchwartzMap.seminorm ℂ k m (S R - g) ≤ errorTailBound g k m / max R 1 :=
      seminorm_truncate_sub_le g hR0 hRone k m
    have harith : errorTailBound g k m / max R 1 < ε := by
      have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
      have hge : errorTailBound g k m / ε + 1 ≤ R := le_trans (le_max_right 1 _) hR
      have hlt : errorTailBound g k m / ε < R := by linarith
      rw [hmax, div_lt_iff₀ hRpos, mul_comm ε R]
      exact (div_lt_iff₀ hε).mp hlt
    exact lt_of_le_of_lt hbound harith
  -- Claim B: push through the continuous map to `Lᵖ`.
  have hLcont : Tendsto (fun R => L (S R)) atTop (𝓝 (L g)) := (L.continuous.tendsto g).comp hSg
  have hnorm : Tendsto (fun R => ‖L (S R) - L g‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R => L (S R) - L g) atTop (𝓝 (0 : Lp ℂ p volume)) := by
      have := hLcont.sub (tendsto_const_nhds (x := L g))
      simpa using this
    simpa using h1.norm
  -- Rewrite the real limit as the toReal of the eLpNorm of the difference.
  have hkey : (fun R => ‖L (S R) - L g‖)
      = fun R => (eLpNorm (⇑(S R - g)) p volume).toReal := by
    funext R
    rw [← map_sub, hL, SchwartzMap.toLpCLM_apply, SchwartzMap.norm_toLp]
  rw [hkey] at hnorm
  -- Lift from `toReal → 0` to `ℝ≥0∞`.
  have hfin : ∀ R, eLpNorm (⇑(S R - g)) p volume ≠ ⊤ :=
    fun R => (SchwartzMap.eLpNorm_lt_top (S R - g) p volume).ne
  have hlift : Tendsto (fun R => eLpNorm (⇑(S R - g)) p volume) atTop (𝓝 0) := by
    have hc := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hnorm
    simp only [ENNReal.ofReal_zero] at hc
    exact hc.congr (fun R => ENNReal.ofReal_toReal (hfin R))
  -- Transfer to the target function for `R ≥ 1`.
  refine hlift.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR1
  have hmax : max R 1 = R := max_eq_left hR1
  have hfun : (⇑(S R - g) : Space → ℂ) = fun x => -((1 - cutoff R x) • g x) := by
    funext x
    rw [hS]
    show cutoff (max R 1) x • g x - g x = -((1 - cutoff R x) • g x)
    rw [hmax, sub_smul, one_smul, neg_sub]
  rw [hfun]
  exact eLpNorm_neg _ _ _

/-! ## §3.  `cutoffLebesgue`: the physical cutoff error in `L¹` and `L²` -/

/-- The vector cutoff error tends to zero in `Lᵖ`, for any `p` with `1 ≤ p`. -/
theorem tendsto_eLpNorm_cutoff_compl_vector (ψ : Fin 3 → SchwartzMap Space ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Tendsto (fun R : ℝ =>
        eLpNorm (fun x => (1 - scaledCutoff baseCutoff R x) • schwartzVector ψ x) p volume)
      atTop (𝓝 0) := by
  classical
  set g : Fin 3 → SchwartzMap Space ℂ :=
    fun i => (ψ i).postcompCLM Complex.ofRealCLM with hg
  have hgapp : ∀ i x, (g i) x = ((ψ i x : ℝ) : ℂ) := by
    intro i x; rw [hg]; simp [SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply]
  -- Pointwise bound: vector norm ≤ sum of scalar (complex) norms.
  have hbound : ∀ (R : ℝ) x,
      ‖(1 - cutoff R x) • schwartzVector ψ x‖ ≤ ∑ i, ‖(1 - cutoff R x) • (g i) x‖ := by
    intro R x
    calc ‖(1 - cutoff R x) • schwartzVector ψ x‖
        = ‖(1 - cutoff R x)‖ * ‖schwartzVector ψ x‖ := norm_smul _ _
      _ ≤ ‖(1 - cutoff R x)‖ * ∑ i, ‖(g i) x‖ := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          refine le_trans (norm_le_sum_norm _) (le_of_eq ?_)
          apply Finset.sum_congr rfl
          intro i _
          rw [schwartzVector_apply, hgapp, Complex.norm_real]
      _ = ∑ i, ‖(1 - cutoff R x)‖ * ‖(g i) x‖ := by rw [Finset.mul_sum]
      _ = ∑ i, ‖(1 - cutoff R x) • (g i) x‖ := by
          apply Finset.sum_congr rfl; intro i _; rw [norm_smul]
  -- The eLpNorm is bounded by the sum of the scalar eLpNorms.
  have hsum_bound : ∀ R : ℝ,
      eLpNorm (fun x => (1 - cutoff R x) • schwartzVector ψ x) p volume
        ≤ ∑ i, eLpNorm (fun x => (1 - cutoff R x) • (g i) x) p volume := by
    intro R
    have hmono : eLpNorm (fun x => (1 - cutoff R x) • schwartzVector ψ x) p volume
        ≤ eLpNorm (fun x => ∑ i, ‖(1 - cutoff R x) • (g i) x‖) p volume :=
      eLpNorm_mono_real (fun x => hbound R x)
    refine le_trans hmono ?_
    have hcont : ∀ i, Continuous (fun x => (1 - cutoff R x) • (g i) x) := by
      intro i
      exact ((continuous_const.sub (cutoff_smooth R).continuous).smul (g i).continuous)
    have hsum_le := eLpNorm_sum_le (μ := volume) (p := p)
      (f := fun i => fun x => ‖(1 - cutoff R x) • (g i) x‖)
      (s := Finset.univ)
      (fun i _ => (hcont i).norm.aestronglyMeasurable) (Fact.out (p := (1 : ℝ≥0∞) ≤ p))
    have hrw : (fun x => ∑ i, ‖(1 - cutoff R x) • (g i) x‖)
        = ∑ i : Fin 3, fun x => ‖(1 - cutoff R x) • (g i) x‖ := by
      funext x; rw [Finset.sum_apply]
    rw [hrw]
    refine le_trans hsum_le (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro i _
    exact eLpNorm_norm _
  -- Each scalar term tends to zero, so the sum does, so the vector term does.
  have hscalar : ∀ i, Tendsto (fun R : ℝ => eLpNorm (fun x => (1 - cutoff R x) • (g i) x) p volume)
      atTop (𝓝 0) := fun i => tendsto_eLpNorm_cutoff_compl (g i) p
  have hsum_tendsto : Tendsto
      (fun R : ℝ => ∑ i, eLpNorm (fun x => (1 - cutoff R x) • (g i) x) p volume)
      atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 3))
      (fun i _ => hscalar i)
    simpa using this
  have htarget : Tendsto
      (fun R : ℝ => eLpNorm (fun x => (1 - cutoff R x) • schwartzVector ψ x) p volume)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_tendsto
      (fun _ => bot_le) (fun R => hsum_bound R)
  -- `scaledCutoff baseCutoff R = cutoff R` definitionally.
  exact htarget

/-- `research/B02/Spec.lean:489-497` `cutoffLebesgue`, `04-whole-space.tex:249`:
both Lebesgue norms of `(1 − χ_R) h_n` tend to zero as `R → ∞`, with
`χ = baseCutoff`.  This is the physical cutoff step that replaces `B01`'s
Leibniz `Hᵐ` estimate. -/
theorem cutoffLebesgue (ψ : Fin 3 → SchwartzMap Space ℝ) :
    Filter.Tendsto
      (fun R : ℝ =>
        eLpNorm (fun x => (1 - scaledCutoff baseCutoff R x) • schwartzVector ψ x) 1 volume)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto
      (fun R : ℝ =>
        eLpNorm (fun x => (1 - scaledCutoff baseCutoff R x) • schwartzVector ψ x) 2 volume)
      Filter.atTop (nhds 0) :=
  ⟨tendsto_eLpNorm_cutoff_compl_vector ψ 1, tendsto_eLpNorm_cutoff_compl_vector ψ 2⟩

/-! ## §4.  The homogeneous-datum chain, restated token-for-token from `Data.lean` -/

/-- `verification/Contracts/V1/Data.lean:99` `SpatialField`. -/
abbrev SpatialField := Space → Space

/-- `verification/Contracts/V1/Data.lean:282` `VectorDistribution`. -/
abbrev VectorDistribution := Fin 3 → 𝓢'(Space, ℂ)

/-- `verification/Contracts/V1/Data.lean:298` `IsSliceDistribution`. -/
def IsSliceDistribution (z : SpatialField) (U : VectorDistribution) : Prop :=
  ∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
    U i ψ = ∫ x : Space, ψ x * ((z x i : ℝ) : ℂ)

/-- `verification/Contracts/V1/Data.lean:324` `IsHomogeneousDatum`. -/
def IsHomogeneousDatum (s : ℝ) (G : FourierData) (u : 𝓢'(Space, ℂ)) : Prop :=
  ∀ φ : SchwartzMap Space ℂ,
    Integrable (fun ξ : Space => φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ)) ∧
      angularFourierDistribution u φ =
        ∫ ξ : Space, φ ξ * (((‖ξ‖ ^ (-s) : ℝ) : ℂ) * G ξ)

/-- `verification/Contracts/V1/Data.lean:358` `IsHomogeneousVectorDatum`. -/
def IsHomogeneousVectorDatum (s : ℝ) (U : VectorDistribution)
    (G : RealVectorSobolev s) : Prop :=
  ∀ i : Fin 3, IsHomogeneousDatum s ((G i : FourierData)) (U i)

/-- `verification/Contracts/V1/Data.lean:367` `IsHomogeneousSliceDatum`. -/
def IsHomogeneousSliceDatum (s : ℝ) (z : SpatialField)
    (G : RealVectorSobolev s) : Prop :=
  ∃ U : VectorDistribution, IsSliceDistribution z U ∧ IsHomogeneousVectorDatum s U G

/-- `verification/Contracts/V1/Data.lean:410` `homogeneousFourierENorm`. -/
def homogeneousFourierENorm (s : ℝ) (z : SpatialField) : ℝ≥0∞ :=
  (∑ i : Fin 3, ∫⁻ ξ : Space,
      ENNReal.ofReal (‖ξ‖ ^ (2 * s) *
        ‖angularFourier (fun x => ((z x i : ℝ) : ℂ)) ξ‖ ^ 2)) ^ ((2 : ℝ)⁻¹)

/-- `research/B02/Spec.lean:237` `SplitRange`. -/
def SplitRange (s : ℝ) : Prop := -3 / 2 < s ∧ s ≤ 0

/-- `research/B02/Spec.lean:231` `lowHighConstant`. -/
def lowHighConstant (s : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(3 : ℝ)) * ∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)

/-! ## §5.  The diagonal assembly, conditional on units 2, 6 and 7 -/

/-- `research/B02/Spec.lean:515-518` `spatialApproxHomogeneous`, `04-whole-space.tex:249`:
compact-smooth real vector fields are dense in `Ḣ^s(R³;R³)` for `s` in
`SplitRange`, measured by the datum norm.  Proved as the **diagonal** of the
manuscript's stage-4 argument, taking as explicit hypotheses the three units not
yet on this branch — `annularSchwartz` (unit 2), `lebesgueHomogeneousDatum` +
`homogeneousDatumSub` (unit 6), `lowHighSplit` (unit 7) — stated token-for-token
from `research/B02/Spec.lean`; the annular fields (unit 1) are the merged
`annularRestriction` / `annularSmoothing`, and `cutoffLebesgue` is proved above.

Given `A` and `η`: restrict `A` to a compact frequency annulus (`annularRestriction`),
smooth it (`annularSmoothing`), realize the smooth annular datum as a Schwartz
field `h_n = schwartzVector ψ` (`annularSchwartz`), then cut off physically:
`(1−χ_R)h_n → 0` in `L¹` and `L²` (`cutoffLebesgue`), so by `lowHighSplit` its
homogeneous Fourier norm tends to `0`; choosing `R` large makes it `< η/4`.  The
compact-smooth approximant is `χ_R h_n = h_n − (1−χ_R)h_n`, whose datum is
`W − H_diff` by `homogeneousDatumSub`, with `‖H_diff‖ₑ` equal to that Fourier norm
(`lebesgueHomogeneousDatum`'s norm clause).  The three annular/cutoff errors sum
to `< η`. -/
theorem spatialApproxHomogeneous_of
    (hAnnularSchwartz : ∀ (s : ℝ) (δ R : ℝ), 0 < δ → δ < R →
        ∀ W : RealVectorSobolev s, IsAnnularDatum δ R W →
      ∃ ψ : Fin 3 → SchwartzMap Space ℝ, IsHomogeneousSliceDatum s (schwartzVector ψ) W)
    (hLebesgueDatum : ∀ s : ℝ, SplitRange s → ∀ k : SpatialField,
        MemLp k 1 volume → MemLp k 2 volume →
      (∃ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G) ∧
        ∀ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G →
          ‖G‖ₑ = homogeneousFourierENorm s k)
    (hDatumSub : ∀ (s : ℝ) (z w : SpatialField) (Z W : RealVectorSobolev s),
        IsHomogeneousSliceDatum s z Z → IsHomogeneousSliceDatum s w W →
          IsHomogeneousSliceDatum s (z - w) (Z - W))
    (hLowHighSplit : ∀ s : ℝ, SplitRange s → ∀ k : SpatialField,
        MemLp k 1 volume → MemLp k 2 volume →
      homogeneousFourierENorm s k ^ (2 : ℝ) ≤
        ENNReal.ofReal (lowHighConstant s) * eLpNorm k 1 volume ^ (2 : ℝ) +
          eLpNorm k 2 volume ^ (2 : ℝ)) :
    ∀ s : ℝ, SplitRange s → ∀ (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
      ∃ (h : SpatialField) (H : RealVectorSobolev s),
        ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ IsHomogeneousSliceDatum s h H ∧ ‖H - A‖ₑ < η := by
  intro s hs A η hη
  obtain ⟨ε, hεpos, hεη⟩ := exists_real_le_enorm hη
  have hqpos : (0 : ℝ) < ε / 4 := by positivity
  have hofqpos : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.mpr hqpos
  -- Step 1: restrict `A` to a compact frequency annulus.
  obtain ⟨δ, R0, Z, hδpos, hδR0, hZrestr, hZA⟩ :=
    annularRestriction s A (ENNReal.ofReal (ε / 4)) hofqpos
  have hZsupp : IsAnnularSupported δ R0 Z := by
    intro i
    filter_upwards [hZrestr i] with ξ hξ
    intro hnot
    rw [hξ]
    exact Set.indicator_of_notMem hnot _
  -- Step 2: smooth the restricted datum inside a slightly larger annulus.
  obtain ⟨δ', R', W, hδ'pos, hδ'δ, hRR', hWdatum, hWZ⟩ :=
    annularSmoothing s δ R0 hδpos hδR0 Z hZsupp (ENNReal.ofReal (ε / 4)) hofqpos
  have hδ'R' : δ' < R' := by linarith
  -- Step 3: realize the smooth annular datum as a Schwartz field.
  obtain ⟨ψ, hψW⟩ := hAnnularSchwartz s δ' R' hδ'pos hδ'R' W hWdatum
  -- The cutoff complement lies in `L¹ ∩ L²`.
  have hmem : ∀ (R : ℝ) (p : ℝ≥0∞),
      MemLp (fun x => (1 - cutoff R x) • schwartzVector ψ x) p volume := by
    intro R p
    refine (schwartzVector_memLp ψ p).mono ?_ ?_
    · exact ((continuous_const.sub (cutoff_smooth R).continuous).smul
        (schwartzVector_contDiff ψ).continuous).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_smul]
      have h1 : ‖(1 - cutoff R x)‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [cutoff_le_one R x])]
        linarith [cutoff_nonneg R x]
      calc ‖(1 - cutoff R x)‖ * ‖schwartzVector ψ x‖
          ≤ 1 * ‖schwartzVector ψ x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖schwartzVector ψ x‖ := one_mul _
  -- Step 4: the cutoff error tends to zero (`cutoffLebesgue`), hence its
  -- homogeneous Fourier norm does (`lowHighSplit`).
  have hF1 : Tendsto (fun R : ℝ =>
      eLpNorm (fun x => (1 - cutoff R x) • schwartzVector ψ x) 1 volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_cutoff_compl_vector ψ 1
  have hF2 : Tendsto (fun R : ℝ =>
      eLpNorm (fun x => (1 - cutoff R x) • schwartzVector ψ x) 2 volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_cutoff_compl_vector ψ 2
  have hzero2 : (0 : ℝ≥0∞) ^ (2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
  have hF1sq : Tendsto (fun R : ℝ =>
      eLpNorm (fun x => (1 - cutoff R x) • schwartzVector ψ x) 1 volume ^ (2 : ℝ))
      atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto (0 : ℝ≥0∞)).comp hF1
    rw [hzero2] at h; exact h
  have hF2sq : Tendsto (fun R : ℝ =>
      eLpNorm (fun x => (1 - cutoff R x) • schwartzVector ψ x) 2 volume ^ (2 : ℝ))
      atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto (0 : ℝ≥0∞)).comp hF2
    rw [hzero2] at h; exact h
  have hRHS : Tendsto (fun R : ℝ =>
      ENNReal.ofReal (lowHighConstant s) *
          eLpNorm (fun x => (1 - cutoff R x) • schwartzVector ψ x) 1 volume ^ (2 : ℝ) +
        eLpNorm (fun x => (1 - cutoff R x) • schwartzVector ψ x) 2 volume ^ (2 : ℝ))
      atTop (𝓝 0) := by
    have hmul := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (lowHighConstant s))
      hF1sq (Or.inr ENNReal.ofReal_ne_top)
    have hadd := hmul.add hF2sq
    simpa using hadd
  have hqpow : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) ^ (2 : ℝ) :=
    ENNReal.rpow_pos hofqpos ENNReal.ofReal_ne_top
  have hev := hRHS.eventually_lt_const hqpow
  obtain ⟨R, hRlt, hR1⟩ := (hev.and (eventually_ge_atTop (1 : ℝ))).exists
  have hHFsq := (hLowHighSplit s hs (fun x => (1 - cutoff R x) • schwartzVector ψ x)
    (hmem R 1) (hmem R 2)).trans_lt hRlt
  have hHF : homogeneousFourierENorm s (fun x => (1 - cutoff R x) • schwartzVector ψ x)
      < ENNReal.ofReal (ε / 4) :=
    (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp hHFsq
  -- Step 5: the homogeneous datum of the compact-smooth approximant.
  obtain ⟨⟨Hdiff, hHdiff⟩, hnormclause⟩ :=
    hLebesgueDatum s hs (fun x => (1 - cutoff R x) • schwartzVector ψ x) (hmem R 1) (hmem R 2)
  have hHdiffe : ‖Hdiff‖ₑ < ENNReal.ofReal (ε / 4) := by
    rw [hnormclause Hdiff hHdiff]; exact hHF
  have hheq : (schwartzVector ψ) - (fun x => (1 - cutoff R x) • schwartzVector ψ x)
      = fun x => cutoff R x • schwartzVector ψ x := by
    funext x
    simp only [Pi.sub_apply]
    rw [sub_smul, one_smul]; abel
  have hdatum : IsHomogeneousSliceDatum s (fun x => cutoff R x • schwartzVector ψ x)
      (W - Hdiff) := by
    have hsub := hDatumSub s (schwartzVector ψ)
      (fun x => (1 - cutoff R x) • schwartzVector ψ x) W Hdiff hψW hHdiff
    rwa [hheq] at hsub
  refine ⟨fun x => cutoff R x • schwartzVector ψ x, W - Hdiff, ?_, ?_, hdatum, ?_⟩
  · exact (cutoff_smooth R).smul (schwartzVector_contDiff ψ)
  · exact (cutoff_hasCompactSupport (lt_of_lt_of_le one_pos hR1)).smul_right
  · -- The total error is below `η`.
    have cvt : ∀ {x : RealVectorSobolev s}, ‖x‖ₑ < ENNReal.ofReal (ε / 4) → ‖x‖ < ε / 4 := by
      intro x hx
      rw [← ofReal_norm x, ENNReal.ofReal_lt_ofReal_iff hqpos] at hx
      exact hx
    have hZA' : ‖Z - A‖ < ε / 4 := cvt hZA
    have hWZ' : ‖W - Z‖ < ε / 4 := cvt hWZ
    have hHdiff' : ‖Hdiff‖ < ε / 4 := cvt hHdiffe
    have htri : ‖(W - Hdiff) - A‖ ≤ ‖W - Z‖ + ‖Z - A‖ + ‖Hdiff‖ := by
      have e : (W - Hdiff) - A = (W - Z) + (Z - A) - Hdiff := by abel
      rw [e]
      calc ‖(W - Z) + (Z - A) - Hdiff‖
          ≤ ‖(W - Z) + (Z - A)‖ + ‖Hdiff‖ := norm_sub_le _ _
        _ ≤ ‖W - Z‖ + ‖Z - A‖ + ‖Hdiff‖ := by gcongr; exact norm_add_le _ _
    have hlt : ‖(W - Hdiff) - A‖ < ε := by
      have := htri; linarith
    calc ‖(W - Hdiff) - A‖ₑ = ENNReal.ofReal ‖(W - Hdiff) - A‖ := (ofReal_norm _).symm
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hεpos).mpr hlt
      _ ≤ η := hεη

end NSFormalization.Section4.B02

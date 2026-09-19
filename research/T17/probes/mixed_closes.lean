import NSFormalization.Section3.T17.Mixed
import Contracts.V1.Correction

noncomputable section
namespace NSFormalization.Section3.T17.MixedProbe
open Set MeasureTheory Metric NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15 NSFormalization.Section3.T16
open NSFormalization.Section3.T13 (fundamentalCube periodize interior_fundamentalCube)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)
open NSFormalization.Paper1.CorrectionForceNorms
open NSFormalization.Paper1.CorrectionMixedNorms
open scoped ContDiff ENNReal Topology

theorem field_force_spatial_memLp (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T δ r : ℝ) (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2) (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x => correctionForce ν v
        (correctionData v x₀ T θ η O θR ε₀) ε (t, x))) p periodicTorusMeasure := by
  exact force_spatial_memLp ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hεtime hεspace

theorem field_force_mixed_bound (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T δ r : ℝ) (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2) (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r)
    (hcube : closure (ball x₀ r) ⊆ interior fundamentalCube) (hε₀ : ε₀ ≤ 1) :
    ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      mixedLebesgueENormT q p (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ≤
        ENNReal.ofReal (mixedConst ν hv x₀ T hθ hη hθc hηc p q * ε ^ (alphaT p q + 1)) := by
  exact force_mixed_bound ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp hr2 hεtime hεspace hcube hε₀

theorem field_mixedConst_nonneg (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ p q, 1 ≤ p → 1 ≤ q → 0 ≤ mixedConst ν hv x₀ T hθ hη hθc hηc p q := by
  exact mixedConst_nonneg ν hv x₀ T hθ hη hθc hηc

example (p q : ℝ≥0∞) : alphaT p q = BlowupDensity.Contracts.V1.alpha p q := rfl

def cubeCentre : Space := WithLp.toLp 2 (fun _ : Fin 3 => (1 / 2 : ℝ))

/-- The quarter-ball around the cube centre has its closure inside the open
fundamental cube; this discharges the geometric premise concretely. -/
theorem closure_ball_cubeCentre :
    closure (ball cubeCentre (1 / 4 : ℝ)) ⊆ interior fundamentalCube := by
  intro y hy
  have hyc : y ∈ closedBall cubeCentre (1 / 4 : ℝ) := closure_ball_subset_closedBall hy
  have hnorm : ‖y - cubeCentre‖ ≤ 1 / 4 := mem_closedBall_iff_norm.mp hyc
  rw [interior_fundamentalCube]
  intro i
  have hcoord : ‖(y - cubeCentre) i‖ ≤ 1 / 4 :=
    le_trans (PiLp.norm_apply_le (y - cubeCentre) i) hnorm
  have hval : (y - cubeCentre) i = y i - 1 / 2 := rfl
  rw [hval, Real.norm_eq_abs, abs_le] at hcoord
  exact ⟨by linarith [hcoord.1], by linarith [hcoord.2]⟩

theorem nonvacuous_mixed :
    ∃ (v : SpaceTimeField) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
      (hv : ContDiff ℝ ∞ v) (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
      (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η),
      v ≠ 0 ∧ 0 < ε₀ ∧
      (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ,
        MemLp (torusLift (fun x => correctionForce 1 v
          (correctionData v cubeCentre 1 θ η O θR ε₀) ε (t, x))) p periodicTorusMeasure) ∧
      (∀ p q, 1 ≤ p → 1 ≤ q → 0 ≤ mixedConst 1 hv cubeCentre 1 hθ hη hθc hηc p q) ∧
      (∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
        mixedLebesgueENormT q p (correctionForce 1 v
          (correctionData v cubeCentre 1 θ η O θR ε₀) ε) ≤
        ENNReal.ofReal (mixedConst 1 hv cubeCentre 1 hθ hη hθc hηc p q *
          ε ^ (alphaT p q + 1))) := by
  obtain ⟨θR, θ, O, hθR, hθsm, hθcs, hθsupp, hOopen, hKO, hθone, hθrange⟩ :=
    exists_originCutoff (K := (∅ : Set Space)) isCompact_empty
  obtain ⟨η, hηsm, hηcs, hηrange, hηone, hηsupp⟩ := exists_timeCutoff
  obtain ⟨ε₁, hε₁pos, hεtime₁, hεspace₁⟩ :=
    exists_threshold hθR (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  let v : SpaceTimeField := fun _ => coordinateVector 0
  have hv : ContDiff ℝ ∞ v := contDiff_const
  have hvdiv : ∀ t : ℝ, ∀ x : Space, spatialDivergence v t x = 0 := by
    intro t x
    simp [spatialDivergence, spatialDerivative, v]
  have hvne : v ≠ 0 := by
    intro h
    have h0 := congrFun h ((0 : ℝ), (0 : Space))
    simp only [v, Pi.zero_apply] at h0
    have hc : (coordinateVector (0 : Fin 3)) (0 : Fin 3) = 0 := by rw [h0]; rfl
    simp [coordinateVector] at hc
  have hvper : IsPeriodicOn univ v := by
    intro z _ k i
    rfl
  have ht : ∀ ε ∈ Ioc (0 : ℝ) (min 1 ε₁), 2 * ε ^ 2 < min (1 : ℝ) 1 :=
    fun ε hε => hεtime₁ ε ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hs : ∀ ε ∈ Ioc (0 : ℝ) (min 1 ε₁), ε * θR < 1 / 4 :=
    fun ε hε => hεspace₁ ε ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  refine ⟨v, θ, η, O, θR, min 1 ε₁, hv, hθsm, hηsm, hθcs, hηcs,
    hvne, lt_min one_pos hε₁pos, ?_, ?_, ?_⟩
  · exact force_spatial_memLp 1 hv cubeCentre 1 1 (1/4) hvper O θR (min 1 ε₁)
      hθsm hηsm hθcs hηcs hθsupp hηsupp (by norm_num) ht hs
  · exact mixedConst_nonneg 1 hv cubeCentre 1 hθsm hηsm hθcs hηcs
  · exact force_mixed_bound 1 hv cubeCentre 1 1 (1/4) hvper O θR (min 1 ε₁)
      hθsm hηsm hθcs hηcs hθsupp hηsupp (by norm_num) ht hs
      closure_ball_cubeCentre (min_le_left _ _)
end NSFormalization.Section3.T17.MixedProbe

#print axioms NSFormalization.Section3.T17.MixedProbe.field_force_spatial_memLp
#print axioms NSFormalization.Section3.T17.MixedProbe.field_force_mixed_bound
#print axioms NSFormalization.Section3.T17.MixedProbe.cubeCentre
#print axioms NSFormalization.Section3.T17.MixedProbe.closure_ball_cubeCentre
#print axioms NSFormalization.Section3.T17.MixedProbe.nonvacuous_mixed

#print axioms NSFormalization.Section3.T17.MixedProbe.field_mixedConst_nonneg

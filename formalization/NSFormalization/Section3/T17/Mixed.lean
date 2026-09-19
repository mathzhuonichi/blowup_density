import NSFormalization.Section3.T17.Energy
import NSFormalization.Section3.T17.ForceSupport
import NSFormalization.Section3.T15.Mixed
import NSFormalization.Paper1.CorrectionMixedNorms

/-! Mixed correction estimates, transported from the single Euclidean copy.
The global smoothness premise is the documented assembly issue G1. -/
noncomputable section
namespace NSFormalization.Section3.T17
open Set MeasureTheory Metric NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15 NSFormalization.Section3.T16
open NSFormalization.Section3.T13 (fundamentalCube periodize)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)
open NSFormalization.Paper1.CorrectionForceNorms
open NSFormalization.Paper1.CorrectionMixedNorms
open scoped ContDiff ENNReal Topology

/-- The finite Paper1 constant, converted to a real constant before choosing ε. -/
def mixedConst (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (p q : ℝ≥0∞) : ℝ :=
  (Classical.choose (physical_force_mixed_bound ν hv x₀ T hθ hη hθc hηc p q)).toReal

theorem mixedConst_nonneg (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ p q, 1 ≤ p → 1 ≤ q → 0 ≤ mixedConst ν hv x₀ T hθ hη hθc hηc p q :=
  fun _ _ _ _ => ENNReal.toReal_nonneg

section Transport
variable (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T δ r : ℝ) (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2) (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r)

include hv hvper hθ hη hθc hηc hθsupp hηsupp hr2 hεtime hεspace

/-- Honest Haar slices, including the essential supremum endpoint. -/
theorem force_spatial_memLp :
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x => correctionForce ν v
        (correctionData v x₀ T θ η O θR ε₀) ε (t, x))) p periodicTorusMeasure := by
  intro p _ ε hε t
  exact memLp_torusLift_of_continuous
    ((force_smooth ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp
      hr2 hεtime hεspace ε hε).continuous.comp (continuous_const.prodMk continuous_id)) p

/-- Canonical mixed estimate with the same real constant as Paper1/I02. -/
theorem force_mixed_bound
    (hcube : closure (ball x₀ r) ⊆ interior fundamentalCube) (hε₀ : ε₀ ≤ 1) :
    ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      mixedLebesgueENormT q p (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ≤
        ENNReal.ofReal (mixedConst ν hv x₀ T hθ hη hθc hηc p q * ε ^ (alphaT p q + 1)) := by
  intro p q _ _ ε hε
  let H := NSFormalization.Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)
  have hH : Continuous H := (physicalForce_smooth ν hv x₀ T ε hθ hη).continuous
  have hc : HasCompactSupport H := physicalForce_compact ν v x₀ T ε hε.1.ne' hθc hηc
  have hs (t : ℝ) : tsupport (fun x => H (t, x)) ⊆ interior fundamentalCube := by
    refine (closure_mono ?_).trans hcube
    intro x hx
    exact ball_subset_ball (hεspace ε hε).le
      ((source_force_tsupport ν v x₀ T hε.1 hθc hηc hθsupp hηsupp
        (subset_tsupport H hx)).2)
  have heq : ∀ t : ℝ, 0 ≤ t → torusLift (fun x => correctionForce ν v
      (correctionData v x₀ T θ η O θR ε₀) ε (t, x)) = torusLift (fun x => H (t, x)) := by
    intro t _
    rw [force_eq (δ := δ) (r := r) hvper hv.contDiffOn hθ hη hθc hηc hθsupp hηsupp
      hr2 hε.1 (hεspace ε hε) (hεtime ε hε)]
    change torusLift (periodize (fun x => H (t, x))) = _
    exact torusLift_congr_cube (fun x hx => periodize_eq_of_mem_interior (hs t) hx)
  rw [mixedLebesgueENormT_eq hH hc heq]
  simp_rw [eLpNorm_torusLift_eq_volume (continuous_slice hH _) ((hs _).trans interior_subset) p]
  have hb := Classical.choose_spec (physical_force_mixed_bound ν hv x₀ T hθ hη hθc hηc p q)
  refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ((hb.2 ε
    ⟨hε.1, hε.2.trans hε₀⟩).trans_eq ?_)
  rw [mixedConst, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb.1.ne]
  have hexp : -2 + 3 / p.toReal + 2 / q.toReal = alphaT p q + 1 := by
    unfold alphaT
    ring
  change ENNReal.ofReal (ε ^ (-2 + 3 / p.toReal + 2 / q.toReal)) * _ =
    _ * ENNReal.ofReal (ε ^ (alphaT p q + 1))
  exact (mul_comm _ _).trans (congrArg (fun a : ℝ =>
    Classical.choose (physical_force_mixed_bound ν hv x₀ T hθ hη hθc hηc p q) *
      ENNReal.ofReal (ε ^ a)) hexp)
end Transport
end NSFormalization.Section3.T17

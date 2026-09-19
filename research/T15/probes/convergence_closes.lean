import NSFormalization.Section3.T15.Convergence
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
Conformance for the proved `q = 1` specialization, plus a genuinely nonzero
compact force and placement.  The full canonical field is not asserted here:
its `q = 2` branch is the residual recorded in `ATTEMPTS_U14.md`.
-/

noncomputable section

namespace NSFormalization.Section3.T15.ConvergenceProbe

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13
open NSFormalization.Section3.T15
open NSFormalization.Source.PacketScaling
open scoped ContDiff ENNReal Topology

/-! ## Literal raw-clause conformance -/

example {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, s < criticalOrder ((1 : ℝ≥0∞).toReal) →
      Tendsto
        (fun ε : ℝ ↦ forceSobolevENormT 1 s
          (periodizedScaledForce f place.x₀ place.T ε))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact forceConvergence_one hf hc place

/-! ## Nonzero compact bump packet -/

def center : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ ↦ (1 / 2 : ℝ))

def spaceBump : ContDiffBump (0 : Space) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def timeBump : ContDiffBump (1 / 2 : ℝ) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def spatialField : Space → Space :=
  fun x ↦ spaceBump x • coordinateVector 0

def force : VelocityField :=
  fun z ↦ timeBump z.1 • spatialField z.2

def carrier : Set Space := Metric.closedBall (0 : Space) (1 / 4)

theorem timeBump_eq_zero {t : ℝ} (ht : t ≤ 0) : timeBump t = 0 := by
  refine timeBump.zero_of_le_dist ?_
  rw [Real.dist_eq, abs_of_nonpos (by linarith : t - 1 / 2 ≤ 0)]
  change (1 / 4 : ℝ) ≤ _
  linarith

theorem spatialField_tsupport : tsupport spatialField ⊆ carrier := by
  have hsub : Function.support spatialField ⊆ Function.support (⇑spaceBump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hzero
    exact hx (by simp [spatialField, hzero])
  have h : tsupport spatialField ⊆ tsupport (⇑spaceBump) := closure_mono hsub
  change tsupport spatialField ⊆ Metric.closedBall (0 : Space) (1 / 4)
  rwa [spaceBump.tsupport_eq] at h

theorem spatialField_contDiff : ContDiff ℝ ∞ spatialField :=
  spaceBump.contDiff.smul contDiff_const

theorem force_contDiff : ContDiff ℝ ∞ force :=
  (timeBump.contDiff.comp contDiff_fst).smul (spatialField_contDiff.comp contDiff_snd)

theorem force_tsupport :
    tsupport force ⊆ tsupport (⇑timeBump) ×ˢ tsupport spatialField := by
  have hsub : Function.support force ⊆
      Function.support (⇑timeBump) ×ˢ Function.support spatialField := by
    intro z hz
    simp only [Function.mem_support] at hz
    constructor
    · simp only [Function.mem_support]
      intro hzero
      exact hz (by simp [force, hzero])
    · simp only [Function.mem_support]
      intro hzero
      exact hz (by simp [force, hzero])
  refine (closure_mono hsub).trans ?_
  rw [closure_prod_eq]
  exact Subset.rfl

theorem force_compactPositiveTime :
    NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport force := by
  have hts := force_tsupport
  have htime : tsupport (⇑timeBump) = Metric.closedBall (1 / 2 : ℝ) (1 / 4) :=
    timeBump.tsupport_eq
  constructor
  · refine IsCompact.of_isClosed_subset ?_ (isClosed_tsupport _) hts
    exact (htime ▸ isCompact_closedBall (1 / 2 : ℝ) (1 / 4)).prod
      ((isCompact_closedBall (0 : Space) (1 / 4)).of_isClosed_subset
        (isClosed_tsupport _) spatialField_tsupport)
  · intro z hz
    obtain ⟨hz1, _⟩ := hts hz
    rw [htime, Metric.mem_closedBall, Real.dist_eq] at hz1
    refine ⟨?_, mem_univ _⟩
    have habs := abs_le.1 hz1
    simp only [mem_Ioi]
    linarith [habs.1]

theorem chartBall_in_cube :
    closure (Metric.ball center (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine Metric.closure_ball_subset_closedBall.trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - center‖ ≤ 3 / 8 := by
    rw [← dist_eq_norm]
    exact hx
  have hcoord : |x i - center i| ≤ 3 / 8 := by
    have h := abs_spaceCoord_le_norm (x - center) i
    change |x i - center i| ≤ ‖x - center‖ at h
    exact h.trans hd
  have hc : center i = 1 / 2 := rfl
  rw [hc, abs_le] at hcoord
  exact ⟨by linarith [hcoord.1], by linarith [hcoord.2]⟩

theorem eps_space : ∀ ε ∈ Ioc (0 : ℝ) (1 / 2), ∀ y ∈ carrier,
    center + ε • y ∈ Metric.ball center (3 / 8) := by
  intro ε hε y hy
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : center + ε • y - center = ε • y := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
  have hyn : ‖y‖ ≤ 1 / 4 := by
    simpa only [carrier, Metric.mem_closedBall, dist_zero_right] using hy
  have hmul : ε * ‖y‖ ≤ (1 / 2 : ℝ) * (1 / 4) :=
    mul_le_mul hε.2 hyn (norm_nonneg _) (by norm_num)
  linarith

def placement : PlacementData (0 : VelocityField) (0 : PressureField) force ∅ where
  T := 1
  time_pos := by norm_num
  chartCenter := center
  chartRadius := 3 / 8
  chartRadius_pos := by norm_num
  chartBall_in_cube := chartBall_in_cube
  x₀ := center
  x₀_mem := by simp
  Kstar := carrier
  Kstar_compact := isCompact_closedBall _ _
  carrier_subset := empty_subset _
  force_projection_subset := by
    intro t x h
    exact spatialField_tsupport (force_tsupport h).2
  ε₀ := 1 / 2
  eps_pos := by norm_num
  eps_le_one := by norm_num
  eps_time := by
    intro ε hε
    have hsquare : ε ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith [hε.1, hε.2]
    nlinarith
  eps_space := eps_space

theorem nonzero_packet_converges_one :
    force (1 / 2, 0) ≠ 0 ∧
      ∀ s : ℝ, s < criticalOrder ((1 : ℝ≥0∞).toReal) →
        Tendsto
          (fun ε : ℝ ↦ forceSobolevENormT 1 s
            (periodizedScaledForce force placement.x₀ placement.T ε))
          (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  constructor
  · have hb : spaceBump (0 : Space) = 1 :=
      spaceBump.one_of_mem_closedBall (by norm_num [spaceBump])
    have ht : timeBump (1 / 2 : ℝ) = 1 :=
      timeBump.one_of_mem_closedBall (by norm_num [timeBump])
    change timeBump (1 / 2 : ℝ) • spatialField (0 : Space) ≠ 0
    rw [ht, one_smul]
    simp [spatialField, hb, coordinateVector]
  · exact forceConvergence_one force_contDiff force_compactPositiveTime placement

end NSFormalization.Section3.T15.ConvergenceProbe

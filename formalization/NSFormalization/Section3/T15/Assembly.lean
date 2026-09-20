import NSFormalization.Section3.T15.Solution
import NSFormalization.Section3.T15.ConvergenceTwo
import NSFormalization.Section3.T15.Blowup

noncomputable section
namespace NSFormalization.Section3.T15
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13
open NSFormalization.Source.PacketScaling
open scoped Topology ContDiff ENNReal

section Placement
variable {u f : VelocityField} {p : PressureField} {K : Set Space}
variable (hK : IsCompact K) (hf : HasCompactSupport f) (T : ℝ) (hT : 0 < T)
def placementCenter : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))
def placementCarrier (K : Set Space) (f : VelocityField) : Set Space := K ∪ Prod.snd '' tsupport f

include hK hf in
theorem placementCarrier_compact : IsCompact (placementCarrier K f) :=
  hK.union (hf.image continuous_snd)

include hK hf in
theorem placementCarrier_bound : ∃ R : ℝ, 0 < R ∧ ∀ y ∈ placementCarrier K f, ‖y‖ ≤ R :=
  (placementCarrier_compact hK hf).isBounded.exists_pos_norm_le

def placementRadius : ℝ := Classical.choose (placementCarrier_bound hK hf)

theorem placementRadius_pos : 0 < placementRadius hK hf := (Classical.choose_spec (placementCarrier_bound hK hf)).1

theorem placement_norm_le_radius {y : Space} (hy : y ∈ placementCarrier K f) : ‖y‖ ≤ placementRadius hK hf :=
  (Classical.choose_spec (placementCarrier_bound hK hf)).2 y hy

def placementThreshold : ℝ := min (min (1 / 2) (T / 4)) (1 / (8 * (placementRadius hK hf + 1)))

include hT in
theorem placementThreshold_pos : 0 < placementThreshold hK hf T := by
  unfold placementThreshold
  exact lt_min (lt_min (by norm_num) (by positivity)) (by have := placementRadius_pos hK hf; positivity)

theorem placement_chart_in_cube :
    closure (Metric.ball placementCenter (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine Metric.closure_ball_subset_closedBall.trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - placementCenter‖ ≤ 3 / 8 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  have hc := abs_spaceCoord_le_norm (x - placementCenter) i
  have hcoord : (x - placementCenter) i = x i - 1 / 2 := rfl
  rw [hcoord] at hc
  have h := abs_le.mp (hc.trans hd)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

def placementData : PlacementData u p f K where
  T := T
  time_pos := hT
  chartCenter := placementCenter
  chartRadius := 3 / 8
  chartRadius_pos := by norm_num
  chartBall_in_cube := placement_chart_in_cube
  x₀ := placementCenter
  x₀_mem := by simp
  Kstar := placementCarrier K f
  Kstar_compact := placementCarrier_compact hK hf
  carrier_subset := subset_union_left
  force_projection_subset := fun t x hx => Or.inr ⟨(t, x), hx, rfl⟩
  ε₀ := placementThreshold hK hf T
  eps_pos := placementThreshold_pos hK hf T hT
  eps_le_one := (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))
  eps_time := by
    intro ε hε
    have he : ε ≤ 1 / 2 := hε.2.trans ((min_le_left _ _).trans (min_le_left _ _))
    have ht : ε ≤ T / 4 := hε.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    nlinarith [mul_nonneg hε.1.le (sub_nonneg.mpr he)]
  eps_space := by
    intro ε hε y hy
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : placementCenter + ε • y - placementCenter = ε • y := by abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
    have hden : 0 < 8 * (placementRadius hK hf + 1) := by have := placementRadius_pos hK hf; positivity
    have he : ε * (8 * (placementRadius hK hf + 1)) ≤ 1 :=
      (le_div_iff₀ hden).mp (hε.2.trans (min_le_right _ _))
    have hn := mul_le_mul_of_nonneg_left (placement_norm_le_radius hK hf hy) hε.1.le
    nlinarith [hε.1]

/-- The reference horizon is preserved definitionally. -/
theorem placementData_time : (placementData (u := u) (p := p) hK hf T hT).T = T := rfl

end Placement

/-- All 21 fields. The union of raw inputs is I03's eight energy clauses,
pressure support and extension smoothness, force smoothness/positive compact
support/nonpositive-time vanishing, extended momentum/divergence and blowup. -/
def scalingAPI {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} {M D : ℝ}
    (hP : NSFormalization.Section4.I03.PacketData u K M D)
    (hp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => p (t, x)) ⊆ K)
    (hps : ContDiffOn ℝ ∞ (zeroPastField p) (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hz : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, f (t, x) = 0)
    (heq : ∀ t : ℝ, t < 1 → ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (zeroPastField u) (zeroPastField p) t x = zeroPastField f (t, x))
    (hdiv : ∀ t : ℝ, t < 1 → ∀ x : Space, spatialDivergence (zeroPastField u) t x = 0)
    (hb : SpeedUnboundedAtOne u) (place : PlacementData u p f K) :
    ScalingAPI (ν := ν) u p f K M D place where
  localization := NSFormalization.Section3.T13.localizationAPI
  velocity_summable := velocity_summable hP.carrier_compact hP.support place
  pressure_summable := pressure_summable hP.carrier_compact hp place
  force_summable := force_summable hc place
  velocity_singleCopy := velocity_singleCopy hP.carrier_compact hP.support place
  pressure_singleCopy := pressure_singleCopy hP.carrier_compact hp place
  force_singleCopy := force_singleCopy hc place
  force_mem := force_mem hf hc place
  solution := solution hP.carrier_compact hP.support hp hc hz hP.extension_smooth hps heq hdiv place
  pressureSlice_integrable := pressureSlice_integrable hP.carrier_compact hp hps place
  unboundedSpeed := unboundedSpeed hP.carrier_compact hP.support hb place
  energySlices_memLp := energySlices_memLp hP.extension_smooth hP.carrier_compact hP.support place
  packetEnergyIdentity := packetEnergyIdentity hP hP.support place
  packetDissipationIdentity := packetDissipationIdentity hP hP.support place
  mixed_memLp := mixed_memLp hf hc place
  packetMixedScaling := packetMixedScaling hf hc place
  sobolevConst := sobolevConst f
  sobolevConst_pos := sobolevConst_pos f
  forceSobolev_memLp := forceSobolev_memLp hf hc place
  packetSobolevBound := packetSobolevBound hf hc place
  forceConvergence := forceConvergence hf hc place

/-- The canonical raw-clause statement, with no additional assumptions. -/
theorem scalingStatement_holds : scalingStatement := by
  intro ν _ u p f K M D τ _ _ hf hc hK hu hp hi _ _ hb hsq hM hDi hD
    _ _ _ _ _ hz hus hps heq hdiv _ _ place
  exact ⟨scalingAPI ⟨hus, hK, hu, hsq, hi, hM, hDi, hD⟩ hp hps hf hc hz heq hdiv hb place⟩

end NSFormalization.Section3.T15

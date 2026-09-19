import NSFormalization.Section3.T15.Pressure
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
Reviewer non-vacuity check for lane 447.

Unlike the lane's time-independent concrete pressure, `revPressure` vanishes
smoothly at nonpositive times.  It is nonzero, has the same compact spatial
support, and instantiates the lane's two main theorems on inhabited scale and
time intervals.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Source.PacketScaling
open scoped ContDiff Topology

def revCenter : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))

def revBump : ContDiffBump (0 : Space) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def revPressure : PressureField :=
  fun z => expNegInvGlue z.1 * revBump z.2

def revZeroVelocity : VelocityField := fun _ => 0

def revZeroForce : VelocityField := fun _ => 0

def revCarrier : Set Space := Metric.closedBall (0 : Space) (1 / 4)

theorem revPressure_zeroPast : zeroPastField revPressure = revPressure := by
  funext z
  by_cases hz : 0 < z.1
  · simp [zeroPastField, revPressure, hz]
  · have hz' : z.1 <= 0 := le_of_not_gt hz
    simp [zeroPastField, revPressure, hz, expNegInvGlue.zero_of_nonpos hz']

theorem revPressure_extension_smooth :
    ContDiffOn ℝ ∞ (zeroPastField revPressure)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)) := by
  rw [revPressure_zeroPast]
  exact ((expNegInvGlue.contDiff.comp contDiff_fst).mul
    (revBump.contDiff.comp contDiff_snd)).contDiffOn

theorem revPressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => revPressure (t, x)) ⊆ revCarrier := by
  intro t _
  exact (tsupport_mul_subset_right.trans revBump.tsupport_eq.subset)

theorem rev_chartBall_in_cube :
    closure (Metric.ball revCenter (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - revCenter‖ ≤ 3 / 8 := by
    rw [← dist_eq_norm]
    exact hx
  have h1 : |x i - revCenter i| ≤ 3 / 8 := by
    have h := abs_spaceCoord_le_norm (x - revCenter) i
    have h2 : (x - revCenter) i = x i - revCenter i := rfl
    rw [h2] at h
    linarith
  have hc : revCenter i = 1 / 2 := rfl
  rw [hc, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem rev_eps_space : ∀ ε ∈ Ioc (0 : ℝ) (1 / 2), ∀ y ∈ revCarrier,
    revCenter + ε • y ∈ Metric.ball revCenter (3 / 8) := by
  intro ε hε y hy
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : revCenter + ε • y - revCenter = ε • y := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
  have hyn : ‖y‖ ≤ 1 / 4 := by
    simpa only [revCarrier, Metric.mem_closedBall, dist_zero_right] using hy
  have h1 : ε * ‖y‖ ≤ (1 / 2 : ℝ) * (1 / 4) :=
    mul_le_mul hε.2 hyn (norm_nonneg _) (by norm_num)
  linarith

def revPlacement :
    PlacementData revZeroVelocity revPressure revZeroForce revCarrier where
  T := 1
  time_pos := by norm_num
  chartCenter := revCenter
  chartRadius := 3 / 8
  chartRadius_pos := by norm_num
  chartBall_in_cube := rev_chartBall_in_cube
  x₀ := revCenter
  x₀_mem := by simp
  Kstar := revCarrier
  Kstar_compact := isCompact_closedBall _ _
  carrier_subset := Subset.rfl
  force_projection_subset := by
    intro t x h
    have hz : tsupport revZeroForce = (∅ : Set SpaceTime) := by
      have hs : Function.support revZeroForce = (∅ : Set SpaceTime) := by
        exact Function.support_eq_empty_iff.mpr rfl
      simp [tsupport, hs]
    rw [hz] at h
    exact h.elim
  ε₀ := 1 / 2
  eps_pos := by norm_num
  eps_le_one := by norm_num
  eps_time := by
    intro ε hε
    have hprod : 0 ≤ (1 / 2 - ε) * (1 / 2 + ε) :=
      mul_nonneg (sub_nonneg.mpr hε.2) (add_nonneg (by norm_num) hε.1.le)
    have hsquare : ε ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
    nlinarith
  eps_space := rev_eps_space

theorem revPressure_nonzero : revPressure ((1 / 2 : ℝ), (0 : Space)) ≠ 0 := by
  have hb : revBump (0 : Space) = 1 :=
    revBump.one_of_mem_closedBall (by simp [revBump])
  unfold revPressure
  rw [hb]
  exact mul_ne_zero (ne_of_gt (expNegInvGlue.pos_of_pos (by norm_num))) one_ne_zero

theorem rev447_main_integrable :
    Integrable
      (torusLift
        (fun x => periodizedScaledPressure revPressure revPlacement.x₀
          revPlacement.T (1 / 4 : ℝ) ((1 / 2 : ℝ), x)))
      periodicTorusMeasure := by
  exact pressureSlice_integrable (isCompact_closedBall _ _) revPressure_support
    revPressure_extension_smooth revPlacement (1 / 4) (by
      norm_num [revPlacement]) (1 / 2) (by
      norm_num [revPlacement])

theorem rev447_main_gauge :
    pressureMeanT
      (normalizedScaledPressure revPressure revPlacement.x₀ revPlacement.T (1 / 4))
      (1 / 2) = 0 := by
  have hg := pressure_gauge (isCompact_closedBall _ _) revPressure_support
    revPressure_extension_smooth revPlacement (1 / 4) (by
      norm_num [revPlacement])
  exact hg (1 / 2) (by norm_num [revPlacement])

end NSFormalization.Section3.T15

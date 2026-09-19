import NSFormalization.Section3.T15.Pressure
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# T15 U10 conformance and concrete pressure-gauge probe

The first two examples copy the canonical pressure-integrability field and the
`ClassicalSolutionT.pressure_gauge` type and close them by bare `exact`.

The concrete part repeats the pressure and geometry of
`placement_closes.lean`: the spatial `ContDiffBump`, cube centre, support ball,
and active placement are identical.  As that earlier placement-only probe uses
a time-independent pressure, its past-zero extension is discontinuous at time
zero.  Here integrability is checked slicewise (which is all normalization
needs), and the resulting normalized pressure has the full gauge on `[0,1)`.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Source.PacketScaling
open scoped ContDiff Topology

/-! ## Literal consumer checks -/

section FieldChecks

variable {u f : VelocityField} {p : PressureField} {K : Set Space}
variable (hK : IsCompact K)
variable (hp : ∀ t ∈ Ico (0 : ℝ) 1,
  tsupport (fun x : Space ↦ p (t, x)) ⊆ K)
variable (hps : ContDiffOn ℝ ∞ (zeroPastField p)
  (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
variable (place : PlacementData u p f K)

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T,
      Integrable
        (torusLift
          (fun x ↦ periodizedScaledPressure p place.x₀ place.T ε (t, x)))
        periodicTorusMeasure := by
  exact pressureSlice_integrable hK hp hps place

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    PressureGaugeT (Ico (0 : ℝ) place.T)
      (normalizedScaledPressure p place.x₀ place.T ε) := by
  exact pressure_gauge hK hp hps place

end FieldChecks

/-! ## The explicit `placement_closes` bump and geometry -/

def pcCenter : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ ↦ (1 / 2 : ℝ))

def pcBump : ContDiffBump (0 : Space) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def pcPres : PressureField := fun z ↦ pcBump z.2

def pcZeroVelocity : VelocityField := fun _ ↦ 0

def pcZeroForce : VelocityField := fun _ ↦ 0

def pcCarrier : Set Space := Metric.closedBall (0 : Space) (1 / 4)

theorem pcPres_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space ↦ pcPres (t, x)) ⊆ pcCarrier := by
  intro t _
  have he : (fun x : Space ↦ pcPres (t, x)) = (⇑pcBump) := rfl
  rw [he]
  exact pcBump.tsupport_eq.subset

theorem pc_chartBall_in_cube :
    closure (Metric.ball pcCenter (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - pcCenter‖ ≤ 3 / 8 := by
    rw [← dist_eq_norm]
    exact hx
  have h1 : |x i - pcCenter i| ≤ 3 / 8 := by
    have h := abs_spaceCoord_le_norm (x - pcCenter) i
    have h2 : (x - pcCenter) i = x i - pcCenter i := rfl
    rw [h2] at h
    linarith
  have hc : pcCenter i = 1 / 2 := rfl
  rw [hc, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem pc_eps_space : ∀ ε ∈ Ioc (0 : ℝ) (1 / 2), ∀ y ∈ pcCarrier,
    pcCenter + ε • y ∈ Metric.ball pcCenter (3 / 8) := by
  intro ε hε y hy
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : pcCenter + ε • y - pcCenter = ε • y := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
  have hyn : ‖y‖ ≤ 1 / 4 := by
    simpa only [pcCarrier, Metric.mem_closedBall, dist_zero_right] using hy
  have h1 : ε * ‖y‖ ≤ (1 / 2 : ℝ) * (1 / 4) :=
    mul_le_mul hε.2 hyn (norm_nonneg _) (by norm_num)
  linarith

def pcPlacement : PlacementData pcZeroVelocity pcPres pcZeroForce pcCarrier where
  T := 1
  time_pos := by norm_num
  chartCenter := pcCenter
  chartRadius := 3 / 8
  chartRadius_pos := by norm_num
  chartBall_in_cube := pc_chartBall_in_cube
  x₀ := pcCenter
  x₀_mem := by simp
  Kstar := pcCarrier
  Kstar_compact := isCompact_closedBall _ _
  carrier_subset := Subset.rfl
  force_projection_subset := by
    intro t x h
    have hz : tsupport pcZeroForce = (∅ : Set SpaceTime) := by
      have hs : Function.support pcZeroForce = (∅ : Set SpaceTime) := by
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
  eps_space := pc_eps_space

theorem pc_scaledPressure_slice_contDiff (ε t : ℝ) :
    ContDiff ℝ ∞ (fun x : Space ↦ scaledPressure pcPres pcCenter 1 ε (t, x)) := by
  by_cases hs : 0 < (ε⁻¹) ^ 2 * (t - (1 - ε ^ 2))
  · have hs' : 0 < (ε ^ 2)⁻¹ * (t - (1 - ε ^ 2)) := by
      simpa only [inv_pow] using hs
    have heq : (fun x : Space ↦ scaledPressure pcPres pcCenter 1 ε (t, x)) =
        fun x ↦ (ε⁻¹) ^ 2 * pcBump (ε⁻¹ • (x - pcCenter)) := by
      funext x
      simp [scaledPressure, scaledSourcePoint, scaledStartTime, zeroPastField,
        pcPres, hs']
    rw [heq]
    have haff : ContDiff ℝ ∞ (fun x : Space ↦ ε⁻¹ • (x - pcCenter)) := by
      fun_prop
    exact contDiff_const.mul (pcBump.contDiff.comp haff)
  · have hs' : ¬ 0 < (ε ^ 2)⁻¹ * (t - (1 - ε ^ 2)) := by
      simpa only [inv_pow] using hs
    have heq : (fun x : Space ↦ scaledPressure pcPres pcCenter 1 ε (t, x)) =
        fun _ ↦ 0 := by
      funext x
      simp [scaledPressure, scaledSourcePoint, scaledStartTime, zeroPastField,
        hs']
    rw [heq]
    exact contDiff_const

/-- Raw slice integrability for the exact time-independent pressure used by
`placement_closes.lean`; temporal smoothness is deliberately irrelevant here. -/
theorem pc_pressureSlice_integrable :
    ∀ ε ∈ Ioc (0 : ℝ) pcPlacement.ε₀,
      ∀ t ∈ Ico (0 : ℝ) pcPlacement.T,
        Integrable
          (torusLift
            (fun x ↦ periodizedScaledPressure pcPres pcPlacement.x₀
              pcPlacement.T ε (t, x)))
          periodicTorusMeasure := by
  intro ε hε t ht
  apply periodizedScaledPressure_slice_integrable
  · exact scaledPressure_slice_subset_cube hε (isCompact_closedBall _ _)
      pcPres_support Subset.rfl pc_eps_space pc_chartBall_in_cube ht.2
  · exact pc_scaledPressure_slice_contDiff ε t

/-- The normalized pressure of the concrete `placement_closes` bump satisfies
the full `ClassicalSolutionT` gauge time-domain at every admissible scale. -/
theorem pc_pressure_gauge :
    ∀ ε ∈ Ioc (0 : ℝ) pcPlacement.ε₀,
      PressureGaugeT (Ico (0 : ℝ) pcPlacement.T)
        (normalizedScaledPressure pcPres pcPlacement.x₀ pcPlacement.T ε) := by
  intro ε hε
  exact normalizePressureT_pressureGauge (pc_pressureSlice_integrable ε hε)

end NSFormalization.Section3.T15

import NSFormalization.Section3.T15.SingleCopy
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# T15 U3 conformance and concrete active-time probe

The first six examples copy the six canonical `ScalingAPI` field types and
close them by a bare `exact` of the corresponding U3 theorem.  The last part
uses the same bump, cube centre, support ball, scale `ε = 1/2`, and active time
`t = 7/8` as `placement_closes.lean`.  Here `ε₀` is shrunk to `1/2`, which also
allows those data to form a complete canonical `PlacementData` witness.

Run from `verification/` with
`lake env lean ../research/T15/probes/single_copy_closes.lean`.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Source.PacketScaling
open scoped Topology

/-! ## Six literal `ScalingAPI` field-type checks -/

section FieldChecks

variable {u f : VelocityField} {p : PressureField} {K : Set Space}
variable (hK : IsCompact K)
variable (hu : ∀ t ∈ Ico (0 : ℝ) 1,
  tsupport (fun x : Space => u (t, x)) ⊆ K)
variable (hp : ∀ t ∈ Ico (0 : ℝ) 1,
  tsupport (fun x : Space => p (t, x)) ⊆ K)
variable (hf : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
variable (place : PlacementData u p f K)

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x : Space,
      Summable (fun n : PeriodicFrequency ↦
        scaledVelocity u place.x₀ place.T ε (t, x - latticeVector n)) := by
  exact velocity_summable hK hu place

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x : Space,
      Summable (fun n : PeriodicFrequency ↦
        scaledPressure p place.x₀ place.T ε (t, x - latticeVector n)) := by
  exact pressure_summable hK hp place

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, ∀ x : Space,
      Summable (fun n : PeriodicFrequency ↦
        scaledForce f place.x₀ place.T ε (t, x - latticeVector n)) := by
  exact force_summable hf place

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x ∈ fundamentalCube,
      periodizedScaledVelocity u place.x₀ place.T ε (t, x) =
        scaledVelocity u place.x₀ place.T ε (t, x) := by
  exact velocity_singleCopy hK hu place

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, t < place.T → ∀ x ∈ fundamentalCube,
      periodizedScaledPressure p place.x₀ place.T ε (t, x) =
        scaledPressure p place.x₀ place.T ε (t, x) := by
  exact pressure_singleCopy hK hp place

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    ∀ t : ℝ, ∀ x ∈ fundamentalCube,
      periodizedScaledForce f place.x₀ place.T ε (t, x) =
        scaledForce f place.x₀ place.T ε (t, x) := by
  exact force_singleCopy hf place

end FieldChecks

/-! ## The `placement_closes` geometry at an active time -/

def scCenter : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))

def scBump : ContDiffBump (0 : Space) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def scField : Space → Space := fun x => scBump x • coordinateVector 0

def scVelocity : VelocityField := fun z => scField z.2

def scPressure : PressureField := fun z => scBump z.2

def scForce : VelocityField := fun _ => 0

def scCarrier : Set Space := Metric.closedBall (0 : Space) (1 / 4)

theorem scField_tsupport : tsupport scField ⊆ scCarrier := by
  have hsub : Function.support scField ⊆ Function.support (⇑scBump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hz
    exact hx (by simp [scField, hz])
  have h : tsupport scField ⊆ tsupport (⇑scBump) := closure_mono hsub
  change tsupport scField ⊆ Metric.closedBall (0 : Space) (1 / 4)
  rwa [scBump.tsupport_eq] at h

theorem scVelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => scVelocity (t, x)) ⊆ scCarrier := by
  intro t _
  have he : (fun x : Space => scVelocity (t, x)) = scField := rfl
  rw [he]
  exact scField_tsupport

theorem scPressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => scPressure (t, x)) ⊆ scCarrier := by
  intro t _
  have he : (fun x : Space => scPressure (t, x)) = (⇑scBump) := rfl
  rw [he]
  change tsupport (⇑scBump) ⊆ Metric.closedBall (0 : Space) (1 / 4)
  exact scBump.tsupport_eq.subset

theorem sc_chartBall_in_cube :
    closure (Metric.ball scCenter (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - scCenter‖ ≤ 3 / 8 := by
    rw [← dist_eq_norm]
    exact hx
  have h1 : |x i - scCenter i| ≤ 3 / 8 := by
    have h := abs_spaceCoord_le_norm (x - scCenter) i
    have h2 : (x - scCenter) i = x i - scCenter i := rfl
    rw [h2] at h
    linarith
  have hc : scCenter i = 1 / 2 := rfl
  rw [hc, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

theorem sc_eps_space : ∀ ε ∈ Ioc (0 : ℝ) (1 / 2), ∀ y ∈ scCarrier,
    scCenter + ε • y ∈ Metric.ball scCenter (3 / 8) := by
  intro ε hε y hy
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : scCenter + ε • y - scCenter = ε • y := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
  have hyn : ‖y‖ ≤ 1 / 4 := by
    simpa only [scCarrier, Metric.mem_closedBall, dist_zero_right] using hy
  have h1 : ε * ‖y‖ ≤ (1 / 2 : ℝ) * (1 / 4) :=
    mul_le_mul hε.2 hyn (norm_nonneg _) (by norm_num)
  linarith

theorem scForce_support :
    NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport scForce := by
  have hz : tsupport scForce = (∅ : Set SpaceTime) := by
    have hs : Function.support scForce = (∅ : Set SpaceTime) := by
      change Function.support (fun _ : SpaceTime => (0 : Space)) = ∅
      exact Function.support_eq_empty_iff.mpr rfl
    simp [tsupport, hs]
  constructor
  · rw [HasCompactSupport, hz]
    exact isCompact_empty
  · rw [hz]
    exact empty_subset _

def scPlacement : PlacementData scVelocity scPressure scForce scCarrier where
  T := 1
  time_pos := by norm_num
  chartCenter := scCenter
  chartRadius := 3 / 8
  chartRadius_pos := by norm_num
  chartBall_in_cube := sc_chartBall_in_cube
  x₀ := scCenter
  x₀_mem := by simp
  Kstar := scCarrier
  Kstar_compact := isCompact_closedBall _ _
  carrier_subset := Subset.rfl
  force_projection_subset := by
    intro t x h
    have hz : tsupport scForce = (∅ : Set SpaceTime) := by
      have hs : Function.support scForce = (∅ : Set SpaceTime) := by
        change Function.support (fun _ : SpaceTime => (0 : Space)) = ∅
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
  eps_space := sc_eps_space

theorem scCenter_mem_cube : scCenter ∈ fundamentalCube := by
  intro i
  have hi : scCenter i = 1 / 2 := rfl
  rw [hi]
  constructor <;> norm_num

/-- All six U3 conclusions on the explicit geometry, at `ε=1/2`, active time
`t=7/8`, and the cube centre. -/
theorem single_copy_closes :
    Summable (fun n : PeriodicFrequency =>
      scaledVelocity scVelocity scPlacement.x₀ scPlacement.T (1 / 2)
        (7 / 8, scCenter - latticeVector n)) ∧
    Summable (fun n : PeriodicFrequency =>
      scaledPressure scPressure scPlacement.x₀ scPlacement.T (1 / 2)
        (7 / 8, scCenter - latticeVector n)) ∧
    Summable (fun n : PeriodicFrequency =>
      scaledForce scForce scPlacement.x₀ scPlacement.T (1 / 2)
        (7 / 8, scCenter - latticeVector n)) ∧
    periodizedScaledVelocity scVelocity scPlacement.x₀ scPlacement.T (1 / 2)
        (7 / 8, scCenter) =
      scaledVelocity scVelocity scPlacement.x₀ scPlacement.T (1 / 2)
        (7 / 8, scCenter) ∧
    periodizedScaledPressure scPressure scPlacement.x₀ scPlacement.T (1 / 2)
        (7 / 8, scCenter) =
      scaledPressure scPressure scPlacement.x₀ scPlacement.T (1 / 2)
        (7 / 8, scCenter) ∧
    periodizedScaledForce scForce scPlacement.x₀ scPlacement.T (1 / 2)
        (7 / 8, scCenter) =
      scaledForce scForce scPlacement.x₀ scPlacement.T (1 / 2)
        (7 / 8, scCenter) := by
  have hε : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) scPlacement.ε₀ := by
    change (1 / 2 : ℝ) ∈ Ioc 0 (1 / 2)
    norm_num
  have ht : (7 / 8 : ℝ) < scPlacement.T := by
    change (7 / 8 : ℝ) < 1
    norm_num
  refine ⟨velocity_summable (isCompact_closedBall _ _) scVelocity_support
      scPlacement (1 / 2) hε (7 / 8) ht scCenter,
    pressure_summable (isCompact_closedBall _ _) scPressure_support
      scPlacement (1 / 2) hε (7 / 8) ht scCenter,
    force_summable scForce_support scPlacement (1 / 2) hε (7 / 8) scCenter,
    velocity_singleCopy (isCompact_closedBall _ _) scVelocity_support
      scPlacement (1 / 2) hε (7 / 8) ht scCenter scCenter_mem_cube,
    pressure_singleCopy (isCompact_closedBall _ _) scPressure_support
      scPlacement (1 / 2) hε (7 / 8) ht scCenter scCenter_mem_cube,
    force_singleCopy scForce_support scPlacement
      (1 / 2) hε (7 / 8) scCenter scCenter_mem_cube⟩

/-- The active velocity slice used above is genuinely nonzero, so the
single-copy equality is not a zero-field artefact. -/
example :
    scaledVelocity scVelocity scCenter 1 (1 / 2) (7 / 8, scCenter) ≠ 0 := by
  have hv : scField (0 : Space) ≠ 0 := by
    have hb : scBump (0 : Space) = 1 :=
      scBump.one_of_mem_closedBall (by norm_num [scBump])
    simp [scField, hb, coordinateVector]
  simpa [scaledVelocity, scaledSourcePoint, scaledStartTime, zeroPastField, scVelocity,
    sub_self, smul_zero] using And.intro
      (by norm_num : (1 : ℝ) - (2 ^ 2)⁻¹ < 7 / 8)
      (smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hv)

end NSFormalization.Section3.T15

import NSFormalization.Section3.T15.Placement
import NSFormalization.Section3.T13.ConstantEndpoints
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# T15 U2 consumer probe — explicit geometric placement at an active time

The r1 version took arbitrary containment hypotheses with unused fields.  This
rewrite is the permitted fallback: an **explicit geometric instance** with
concrete numbers (`research/T15/T15_SPLIT.md` U2). This permitted raw-data fallback
realizes the U2-relevant geometric hypotheses with concrete numbers; it is not a full
`PlacementData` witness (with `T = ε₀ = 1` the `eps_time` field would fail at `ε = 1`;
that field is neither used nor claimed here). Fields referenced from
`research/T15/Spec.lean:560-643`:

* the packet velocity/pressure are nonzero `ContDiffBump`s with spatial support
  `closedBall 0 (1/4) = Kstar = carrier`;
* the placement centre `x₀ = chartCenter = pcCenter` is the cube centre
  `(1/2,1/2,1/2)`, chart radius `3/8`, threshold `ε₀ = 1`, singular time `T = 1`;
* `pc_chartBall_in_cube` proves `closure (ball pcCenter (3/8)) ⊆ interior Q`, and
  `pc_eps_space` proves `x₀ + ε • Kstar ⊆ ball pcCenter (3/8)` for `ε ∈ Ioc 0 1`.

`placement_closes` fires the U2 cube/compact-support lemmas at the **active**
time `t = 7/8` (activation `t_ε = 1 - ε² = 3/4 < 7/8`); the separate example
exhibits a genuinely nonzero velocity slice at that time, so the placement is
non-vacuous.

Run: `cd verification && lake env lean ../research/T15/probes/placement_closes.lean`.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Source NSFormalization.Source.PacketScaling
open NSFormalization.Section3.T13
open scoped Topology

/-- Centre of the fundamental cube. -/
def pcCenter : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))

/-- A genuine smooth bump supported in `closedBall 0 (1/4)`. -/
def pcBump : ContDiffBump (0 : Space) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- Nonzero smooth vector packet velocity, spatial support `closedBall 0 (1/4)`. -/
def pcField : Space → Space := fun x => pcBump x • coordinateVector 0

/-- The velocity packet: time-independent bump field. -/
def pcVel : VelocityField := fun z => pcField z.2

/-- The scalar pressure packet: the same bump. -/
def pcPres : PressureField := fun z => pcBump z.2

theorem pcField_tsupport : tsupport pcField ⊆ Metric.closedBall (0 : Space) (1 / 4) := by
  have hsub : Function.support pcField ⊆ Function.support (⇑pcBump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hz
    exact hx (by simp [pcField, hz])
  have h : tsupport pcField ⊆ tsupport (⇑pcBump) := closure_mono hsub
  rwa [pcBump.tsupport_eq] at h

theorem pcVel_slice_tsupport (t : ℝ) :
    tsupport (fun x : Space => pcVel (t, x)) ⊆ Metric.closedBall (0 : Space) (1 / 4) := by
  have he : (fun x : Space => pcVel (t, x)) = pcField := rfl
  rw [he]; exact pcField_tsupport

theorem pcPres_slice_tsupport (t : ℝ) :
    tsupport (fun x : Space => pcPres (t, x)) ⊆ Metric.closedBall (0 : Space) (1 / 4) := by
  have he : (fun x : Space => pcPres (t, x)) = (⇑pcBump) := rfl
  rw [he]; exact pcBump.tsupport_eq.subset

/-- `PlacementData.chartBall_in_cube` for this instance (the same computation as
`research/T15/probes/haar_bridge_closes.lean:42`). -/
theorem pc_chartBall_in_cube :
    closure (Metric.ball pcCenter (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - pcCenter‖ ≤ 3 / 8 := by rw [← dist_eq_norm]; exact hx
  have h1 : |x i - pcCenter i| ≤ 3 / 8 := by
    have h := abs_spaceCoord_le_norm (x - pcCenter) i
    have h2 : (x - pcCenter) i = x i - pcCenter i := rfl
    rw [h2] at h
    linarith
  have hc : pcCenter i = 1 / 2 := rfl
  rw [hc, abs_le] at h1
  exact ⟨by linarith [h1.1], by linarith [h1.2]⟩

/-- `PlacementData.eps_space` for this instance: `x₀ + ε • Kstar ⊆ B`. -/
theorem pc_eps_space : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Metric.closedBall (0 : Space) (1 / 4),
    pcCenter + ε • y ∈ Metric.ball pcCenter (3 / 8) := by
  intro ε hε y hy
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : pcCenter + ε • y - pcCenter = ε • y := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
  have hyn : ‖y‖ ≤ 1 / 4 := by rwa [Metric.mem_closedBall, dist_zero_right] at hy
  have h1 : ε * ‖y‖ ≤ 1 * (1 / 4) := mul_le_mul hε.2 hyn (norm_nonneg _) (by norm_num)
  linarith

/-- The U2 placement API on this explicit geometry, at the active time `t = 7/8`:
the velocity and pressure slices are placed strictly inside `interior Q`, and the
velocity slice has compact support. -/
theorem placement_closes :
    ((1 / 2 : ℝ) ∈ Ioc (0 : ℝ) 1) ∧
    (tsupport (fun x : Space => scaledVelocity pcVel pcCenter 1 (1 / 2) (7 / 8, x)) ⊆
      interior fundamentalCube) ∧
    HasCompactSupport (fun x : Space =>
      scaledVelocity pcVel pcCenter 1 (1 / 2) (7 / 8, x)) ∧
    (tsupport (fun x : Space => scaledPressure pcPres pcCenter 1 (1 / 2) (7 / 8, x)) ⊆
      interior fundamentalCube) := by
  have hεmem : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) 1 := by norm_num
  refine ⟨hεmem, ?_, ?_, ?_⟩
  · exact scaledVelocity_slice_subset_cube (Kstar := Metric.closedBall (0 : Space) (1 / 4))
      hεmem (isCompact_closedBall _ _) (fun t _ => pcVel_slice_tsupport t)
      Subset.rfl pc_eps_space pc_chartBall_in_cube (by norm_num : (7 / 8 : ℝ) < 1)
  · exact scaledVelocity_slice_hasCompactSupport (Kstar := Metric.closedBall (0 : Space) (1 / 4))
      (by norm_num) (isCompact_closedBall _ _) (fun t _ => pcVel_slice_tsupport t)
      Subset.rfl (isCompact_closedBall _ _) (by norm_num : (7 / 8 : ℝ) < 1)
  · exact scaledPressure_slice_subset_cube (Kstar := Metric.closedBall (0 : Space) (1 / 4))
      hεmem (isCompact_closedBall _ _) (fun t _ => pcPres_slice_tsupport t)
      Subset.rfl pc_eps_space pc_chartBall_in_cube (by norm_num : (7 / 8 : ℝ) < 1)

/-- Non-vacuity: at the active time `t = 7/8` (source time `1/2 ∈ (0,1)`) the
velocity slice is genuinely nonzero at the placement centre. -/
example :
    scaledVelocity pcVel pcCenter 1 (1 / 2) (7 / 8, pcCenter) ≠ 0 := by
  have hv : pcField (0 : Space) ≠ 0 := by
    have hb : pcBump (0 : Space) = 1 :=
      pcBump.one_of_mem_closedBall (by norm_num [pcBump])
    simp [pcField, hb, coordinateVector]
  simpa [scaledVelocity, scaledSourcePoint, scaledStartTime, zeroPastField, pcVel,
    sub_self, smul_zero] using And.intro
      (by norm_num : (1 : ℝ) - (2 ^ 2)⁻¹ < 7 / 8)
      (smul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hv)

end NSFormalization.Section3.T15

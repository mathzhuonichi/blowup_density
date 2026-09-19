import NSFormalization.Section3.T17.Correction

/-! G4 still needs the chart-ball inclusion. This probe preserves its exact
hypothesis block and disproves it on an empty packet and a constant reference. -/
noncomputable section
namespace NSFormalization.Section3.T17.GeometryObstruction
open Set Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff Topology

def centre : Space := WithLp.toLp 2 (fun _ : Fin 3 => (1 / 2 : ℝ))

theorem chart_in_cube :
    closure (ball centre (1 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  intro y hy
  have hnorm : ‖y - centre‖ ≤ 1 / 8 :=
    mem_closedBall_iff_norm.mp (closure_ball_subset_closedBall hy)
  rw [interior_fundamentalCube]
  intro i
  have hc := (PiLp.norm_apply_le (y - centre) i).trans hnorm
  change ‖y i - (1 / 2 : ℝ)‖ ≤ 1 / 8 at hc
  rw [Real.norm_eq_abs, abs_le] at hc
  constructor <;> linarith

def place : PlacementData 0 0 0 ∅ where
  T := 1
  time_pos := by norm_num
  chartCenter := centre
  chartRadius := 1 / 8
  chartRadius_pos := by norm_num
  chartBall_in_cube := chart_in_cube
  x₀ := centre
  x₀_mem := by simp
  Kstar := ∅
  Kstar_compact := isCompact_empty
  carrier_subset := Subset.rfl
  force_projection_subset := by simp
  ε₀ := 1 / 8
  eps_pos := by norm_num
  eps_le_one := by norm_num
  eps_time := by
    intro ε hε
    have := hε.1
    have := hε.2
    nlinarith
  eps_space := by simp

theorem ball_not_in_chart :
    ¬ ball place.x₀ (1 / 4 : ℝ) ⊆ ball place.chartCenter place.chartRadius := by
  let y : Space := centre + (3 / 16 : ℝ) • coordinateVector 0
  have hn : ‖y - centre‖ = (3 / 16 : ℝ) := by
    simp [y, norm_smul, coordinateVector]
  intro h
  have hy : y ∈ ball place.x₀ (1 / 4 : ℝ) := by
    change ‖y - centre‖ < (1 / 4 : ℝ)
    rw [hn]
    norm_num
  have hout := h hy
  change ‖y - centre‖ < (1 / 8 : ℝ) at hout
  rw [hn] at hout
  norm_num at hout

def statedG4 : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    0 < ν → 0 < r → r < 1/2 → 0 < δ → IsPeriodicOn univ v →
    ContDiff ℝ ∞ v →
    (∀ t ∈ Ioo 0 (place.T + δ), ∀ x ∈ ball place.x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo 0 1, tsupport (fun x ↦ u (t, x)) ⊆ K) →
    ∃ D, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place v r δ D)

theorem statedG4_false : ¬ statedG4 := by
  intro h
  let v : SpaceTimeField := fun _ => coordinateVector 0
  have hper : IsPeriodicOn univ v := by intro t ht x n; rfl
  obtain ⟨D, _, ⟨A⟩⟩ := h 1 0 0 0 ∅ place v (1/4) 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hper contDiff_const
    (by intros; simp [v, spatialDivergence, spatialDerivative]) (by simp)
  exact ball_not_in_chart A.ball_in_chart

theorem reference_nonzero : (fun _ : SpaceTime => coordinateVector (0 : Fin 3)) ≠ 0 := by
  intro h
  have hv := congrFun h (0, 0)
  have hc := congrArg (fun x : Space => x (0 : Fin 3)) hv
  norm_num [coordinateVector] at hc

end NSFormalization.Section3.T17.GeometryObstruction


#print axioms NSFormalization.Section3.T17.GeometryObstruction.chart_in_cube
#print axioms NSFormalization.Section3.T17.GeometryObstruction.place
#print axioms NSFormalization.Section3.T17.GeometryObstruction.ball_not_in_chart
#print axioms NSFormalization.Section3.T17.GeometryObstruction.statedG4_false
#print axioms NSFormalization.Section3.T17.GeometryObstruction.reference_nonzero

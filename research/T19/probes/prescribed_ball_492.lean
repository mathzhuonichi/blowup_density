import NSFormalization.Section3.T19.FromData
import NSFormalization.Section3.T11.ExtendsBeyond

noncomputable section
namespace Lane492
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Section3.T19
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped ContDiff

theorem zeroInitial : (0 : SpatialField) ∈ initialClassT := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · intro x i
    rfl
  · intro x
    simp [spatialDivergence, spatialDerivative]

theorem zeroForce : (0 : SpaceTimeField) ∈ forceClassT := by
  refine ⟨contDiff_const, ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
  · intro t _ x i
    rfl
  · exact (show tsupport (0 : SpaceTimeField) ⊆ (∅ : Set ℝ) ×ˢ univ by simp)

/-- Applying the entire raw-data theorem supplies a genuine positive threshold
and solutions with lifespan one; no input placement or correction is needed. -/
theorem zero_probe (c : Space) (r : ℝ) (hr : 0 < r)
    (hc : closure (Metric.ball c r) ⊆ interior fundamentalCube) :
    ∃ ε₀ > 0, ∃ force : ℝ → SpaceTimeField,
      ∀ ε ∈ Ioc (0 : ℝ) ε₀,
        force ε ∈ forceClassT ∧ maximalLifespanT 1 0 (force ε) = ENNReal.ofReal 1 := by
  obtain ⟨ε₀, hε₀, force, velocity, M, D, C, R, Cpq, Cs,
    _, _, _, _, _, _, _, hall⟩ :=
    periodicInsertion_from_data 1 (by norm_num) c r hr hc 0 0 zeroInitial zeroForce
      1 1 (by norm_num) (by norm_num)
      (NSFormalization.Section3.T11.constantVelocitySolutionT 0 (by norm_num))
  exact ⟨ε₀, hε₀, force, fun ε hε => ⟨(hall ε hε).1, (hall ε hε).2.2.1⟩⟩

example : ∃ ε₀ > 0, ∃ force : ℝ → SpaceTimeField,
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      force ε ∈ forceClassT ∧ maximalLifespanT 1 0 (force ε) = ENNReal.ofReal 1 :=
  zero_probe placementCenter (3 / 8) (by norm_num) placement_chart_in_cube

def offCenter : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 4 : ℝ))

theorem offCenter_cube : closure (Metric.ball offCenter (1 / 8 : ℝ)) ⊆
    interior fundamentalCube := by
  refine Metric.closure_ball_subset_closedBall.trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - offCenter‖ ≤ 1 / 8 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  have hc := abs_spaceCoord_le_norm (x - offCenter) i
  have hcoord : (x - offCenter) i = x i - 1 / 4 := rfl
  rw [hcoord] at hc
  have h := abs_le.mp (hc.trans hd)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

example : ∃ ε₀ > 0, ∃ force : ℝ → SpaceTimeField,
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      force ε ∈ forceClassT ∧ maximalLifespanT 1 0 (force ε) = ENNReal.ofReal 1 :=
  zero_probe offCenter (1 / 8) (by norm_num) offCenter_cube

end Lane492

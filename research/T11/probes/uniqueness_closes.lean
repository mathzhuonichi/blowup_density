import NSFormalization.Section3.T11.Uniqueness
import NSFormalization.Section3.T11.CriterionBridge

/-! Exact target-shape and non-vacuity probe for T11/U5. -/

noncomputable section

namespace NSFormalization.Section3.T11.UniquenessProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.velocity (t, x) = u₂.velocity (t, x) := by
  exact velocity_unique

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
            u₁.pressure (t, x) = u₂.pressure (t, x) := by
  exact pressure_unique

example
    {horizon : ℝ → SpatialField → SpaceTimeField → ℝ}
    (solution : ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ClassicalSolutionT ν a f (horizon ν a f)) :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ENNReal.ofReal (horizon ν a f) ≤ maximalLifespanT ν a f := by
  exact horizon_le_lifespan solution

/-- All class and solution hypotheses of the uniqueness fields are inhabited
by a genuinely nonzero constant velocity; its realized horizon also
contributes nontrivially to `maximalLifespanT`. -/
example :
    ∃ (a : SpatialField) (f : SpaceTimeField)
      (w : ClassicalSolutionT 1 a f 1),
        a ∈ initialClassT ∧ f ∈ forceClassT ∧
          w.velocity (0, 0) ≠ 0 ∧
          w.velocity (0, 0) = w.velocity (0, 0) ∧
          w.pressure (0, 0) = w.pressure (0, 0) ∧
          ENNReal.ofReal 1 ≤ maximalLifespanT 1 a f := by
  let c : Space := coordinateVector 0
  let a : SpatialField := fun _ ↦ c
  let f : SpaceTimeField := 0
  have hc : c ≠ 0 := by
    intro h
    have h₀ := congrArg (fun v : Space ↦ v (0 : Fin 3)) h
    simp [c, coordinateVector] at h₀
  have ha : a ∈ initialClassT := by
    refine ⟨contDiff_const, fun _ _ ↦ rfl, ?_⟩
    intro x
    simp [a, spatialDivergence, spatialDerivative]
  have hf : f ∈ forceClassT := by
    refine ⟨contDiff_const, fun _ _ _ _ ↦ rfl,
      ∅, isCompact_empty, empty_subset _, ?_⟩
    simp [f]
  let w : ClassicalSolutionT 1 a f 1 := by
    refine
      { velocity := fun _ ↦ c
        pressure := 0
        horizon_pos := zero_lt_one
        velocity_smooth := contDiff_const.contDiffOn
        pressure_smooth := contDiff_const.contDiffOn
        initial := fun _ ↦ rfl
        divergence := ?_
        momentum := ?_
        sobolev := ?_
        pressure_gradient := ?_
        velocity_periodic := fun _ _ _ _ ↦ rfl
        pressure_periodic := fun _ _ _ _ ↦ rfl
        pressure_gauge := ?_ }
    · intro t ht x
      simp [spatialDivergence, spatialDerivative]
    · intro t ht x
      simp [NavierStokesR3.ProblemStatement.navierStokesResidual,
        temporalDerivative, advection, spatialDerivative, spatialLaplacian,
        pressureGradient, f]
    · intro m
      obtain ⟨A, hA⟩ := exists_periodicDatum_smooth (m : ℝ)
        (z := fun _ ↦ c) contDiff_const (fun _ _ ↦ rfl)
      exact ⟨fun _ ↦ A, continuous_const.continuousOn, fun _ _ ↦ hA⟩
    · intro t ht
      have he : (fun x : Space ↦ pressureGradient (0 : SpaceTime → ℝ) t x) = 0 := by
        funext x
        simp [pressureGradient]
      rw [he]
      exact memLp_const (0 : Space)
    · intro t ht
      simp [pressureMeanT, torusLift, NSFormalization.Paper1.torusLift]
  have hvelocity := velocity_unique 1 zero_lt_one a ha f hf 1 1 w w
    0 (by simp) 0
  have hpressure := pressure_unique 1 zero_lt_one a ha f hf 1 1 w w
    0 (by simp) 0
  refine ⟨a, f, w, ha, hf, ?_, hvelocity, hpressure, ?_⟩
  simpa [w] using hc
  exact le_iSup_of_le (1 : ℝ) (le_iSup_of_le ⟨w⟩ le_rfl)

end NSFormalization.Section3.T11.UniquenessProbe

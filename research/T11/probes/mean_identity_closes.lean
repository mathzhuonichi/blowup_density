import NSFormalization.Section3.T11.MeanIdentity
import NSFormalization.Section3.T11.CriterionBridge

/-! Exact target-shape and non-vacuity probe for T11/U7. -/

noncomputable section

namespace NSFormalization.Section3.T11.MeanIdentityProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField IsSolenoidal)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ico (0 : ℝ) T,
            velocityMeanT w.velocity t = galileanMeanT a f t := mean_formula

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            HasDerivAt (velocityMeanT w.velocity) (forceMeanT f t) t := mean_derivative

/-- The class and solution hypotheses used above are simultaneously inhabited
by a genuinely nonzero velocity (with the compactly supported zero force). -/
example :
    ∃ (a : SpatialField) (f : SpaceTimeField)
      (w : ClassicalSolutionT 1 a f 1),
        a ∈ initialClassT ∧ f ∈ forceClassT ∧ w.velocity (0, 0) ≠ 0 := by
  let c : Space := coordinateVector 0
  let a : SpatialField := fun _ ↦ c
  let f : SpaceTimeField := 0
  have hc : c ≠ 0 := by
    intro h
    have h0 := congrArg (fun v : Space ↦ v (0 : Fin 3)) h
    simp [c, coordinateVector] at h0
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
  refine ⟨a, f, w, ha, hf, ?_⟩
  simpa [w] using hc

end NSFormalization.Section3.T11.MeanIdentityProbe

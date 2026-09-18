import NSFormalization.Section3.T11.Maximal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Exact target-shape and non-vacuity probe for T11/U15. -/

noncomputable section

namespace NSFormalization.Section3.T11.MaximalProbe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal

example (H : PeriodicMaximalExistenceInput) : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p := by
  exact exists_maximal H

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (u₁ u₂ : SpaceTimeField) (p₁ p₂ : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u₁ p₁ →
          IsMaximalPeriodicSolution ν a f u₂ p₂ →
            ∀ t : ℝ, 0 ≤ t →
              ENNReal.ofReal t < maximalLifespanT ν a f →
                ∀ x : Space,
                  u₁ (t, x) = u₂ (t, x) ∧ p₁ (t, x) = p₂ (t, x) := by
  exact maximal_unique

example (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) :
    maximalLifespanT ν a f =
      NSFormalization.Paper1.PeriodicLifespan.lifespan ν a f := by
  exact maximalLifespanT_eq_lifespan ν a f

/-- Conditional satisfiability check for the single residual input at a
nonzero datum, a nonzero compact positive-time force, and the resulting
positive-horizon nonzero solution. -/
example (H : PeriodicMaximalExistenceInput) :
    ∃ (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (w : ClassicalSolutionT 1 a f T),
        a ∈ initialClassT ∧ f ∈ forceClassT ∧
          a 0 ≠ 0 ∧ f (2, 0) ≠ 0 ∧ 0 < T ∧ w.velocity (0, 0) ≠ 0 := by
  let profile : ContDiffBump (2 : ℝ) :=
    { rIn := 1 / 4
      rOut := 1 / 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let c : Space := coordinateVector 0
  let a : SpatialField := fun _ ↦ c
  let f : SpaceTimeField := fun z ↦ profile z.1 • c
  have hc : c ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : Space ↦ x 0) h
    simp [c, coordinateVector] at h0
  have ha : a ∈ initialClassT := by
    refine ⟨contDiff_const, fun _ _ ↦ rfl, ?_⟩
    intro x
    simp [a, spatialDivergence, spatialDerivative]
  have hsupport : tsupport (profile : ℝ → ℝ) ⊆ Ioi 0 := by
    rw [profile.tsupport_eq]
    intro t ht
    have habs : |t - 2| ≤ 1 / 2 := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, profile] using ht
    have := (abs_le.mp habs).1
    change 0 < t
    linarith
  have hf : f ∈ forceClassT := by
    exact memForceT_time_smul profile.contDiff profile.hasCompactSupport hsupport
      contDiff_const (fun _ _ ↦ rfl)
  have hf2 : f (2, 0) ≠ 0 := by
    have hp : profile 2 = 1 := profile.one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_self]
      exact profile.rIn_pos.le)
    simpa only [f, hp, one_smul] using hc
  obtain ⟨T, hT, ⟨w⟩⟩ := H 1 zero_lt_one a ha f hf
  refine ⟨a, f, T, w, ha, hf, ?_, hf2, hT, ?_⟩
  · simpa [a] using hc
  · rw [w.initial]
    simpa [a] using hc

end NSFormalization.Section3.T11.MaximalProbe

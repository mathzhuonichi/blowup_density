import NSFormalization.Section3.T11.RestartBeyond
open Set
open NSFormalization.Section3.T11
open NSFormalization.Section4.A02
open NSFormalization.Section3.T10
open NavierStokes.ProblemStatement
open scoped ENNReal
-- Substantive mutation: changing the conclusion horizon from S + δ to S + 2*δ
-- cannot be discharged by the existing restartBeyond theorem.
example (H : PeriodicQuantitativeLocalInput') :
    ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (u : SpaceTimeField) (p : SpaceTimeScalar), SolvesBelowT ν a f S u p →
          (∀ t ∈ Ico (0 : ℝ) S, periodicSobolevENorm 1 (fun x => u (t,x)) ≤ K) →
          ∃ v : ClassicalSolutionT ν a f (S + 2*δ), True := by
  intro ν hν f hf S hS K hK
  obtain ⟨δ, hδ, _⟩ := restartBeyond H ν hν f hf S hS K hK
  refine ⟨δ, hδ, ?_⟩
  intro a ha u p hs hb
  obtain ⟨d, hd, hrest⟩ := restartBeyond H ν hν f hf S hS K hK
  exact (hrest a ha u p hs hb)

import NSFormalization.Section3.T19.FromData

noncomputable section
namespace Lane492Review

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13
open NSFormalization.Section3.T19
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

/-- Deliberately false mutation: replace exact lifespan `T` by `T + δ`. -/
theorem lifespan_constant_mutation
    (ν : ℝ) (hν : 0 < ν) (center : Space) (radius : ℝ) (hρ : 0 < radius)
    (hcube : closure (Metric.ball center radius) ⊆ interior fundamentalCube)
    (a : SpatialField) (g : SpaceTimeField) (ha : a ∈ initialClassT)
    (hg : g ∈ forceClassT) (T δ : ℝ) (hT : 0 < T) (hδ : 0 < δ)
    (reference : ClassicalSolutionT ν a g (T + δ)) :
    ∃ ε₀ > 0, ∃ force : ℝ → SpaceTimeField, ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      maximalLifespanT ν a (force ε) = ENNReal.ofReal (T + δ) := by
  obtain ⟨ε₀, hε₀, force, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hall⟩ :=
    periodicInsertion_from_data ν hν center radius hρ hcube a g ha hg T δ hT hδ reference
  refine ⟨ε₀, hε₀, force, ?_⟩
  intro ε hε
  exact (hall ε hε).2.2.1

end Lane492Review

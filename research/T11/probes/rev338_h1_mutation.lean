import NSFormalization.Section3.T11.ExistenceInputH3

/- Reviewer negative check: changing the proved H³ datum ball to H¹ must not
   silently typecheck through the H³ Picard estimate.  This file is expected to
   fail at the final `exact` with the missing H³-ball hypothesis. -/
noncomputable section
namespace NSFormalization.Section3.T11.Rev338

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal

example :
    ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
          ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
            (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
              ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w := by
  intro ν hν K hK M hM
  refine ⟨picardHorizon ν K M, picardHorizon_pos ν K M, ?_⟩
  intro a ha hKa g hg hgp hMg
  exact exists_classical_on_picardHorizon ν hν K hK M hM a ha hKa g hg hgp hMg

end NSFormalization.Section3.T11.Rev338

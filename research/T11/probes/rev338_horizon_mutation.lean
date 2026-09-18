import NSFormalization.Section3.T11.ExistenceInputH3

/- Lane 338 negative check 2 (worker's own, complementing the reviewer's
   `rev338_h1_mutation.lean`): the horizon's dependence on the FORCE bound is
   load-bearing.  `picardHorizon ν K M` shrinks as `M 3` grows, so the
   force-free horizon `picardHorizon ν K 0` is in general strictly longer and
   the theorem must NOT supply a solution on it.  This file is expected to fail
   at the final `exact`. -/
noncomputable section
namespace NSFormalization.Section3.T11.Rev338Horizon

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal

example :
    ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) →
      ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 3 a ≤ K →
        ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
          (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
            ∃ w : ClassicalSolutionT ν a g (picardHorizon ν K (fun _ ↦ 0)),
              PeriodicLocalRegularity ν a g (picardHorizon ν K (fun _ ↦ 0)) w := by
  intro ν hν K hK M hM a ha hKa g hg hgp hMg
  exact exists_classical_on_picardHorizon ν hν K hK M hM a ha hKa g hg hgp hMg

end NSFormalization.Section3.T11.Rev338Horizon

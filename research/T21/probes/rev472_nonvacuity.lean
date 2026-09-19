import NSFormalization.Section3.T20.Assembly
import NSFormalization.Section3.T21.Assembly

noncomputable section

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ENNReal

namespace NSFormalization.Section3.T21.ReviewerNonvacuity

/- The lane's record is inhabited by the closed canonical T20 package. -/
example : Nonempty (NonDensityAPI
    NSFormalization.Section3.T20.criticalRegularityT.c) :=
  ⟨nonDensityAPI NSFormalization.Section3.T20.criticalRegularityT⟩

/- Stronger than zero-in-the-ball: the critical ball has a nonzero admissible
   force for a positive viscosity, and that force has infinite lifespan. -/
example :
    ∃ ν : ℝ, 0 < ν ∧ ∃ g : SpaceTimeField,
      g ∈ criticalBallT NSFormalization.Section3.T20.criticalRegularityT.c ν (1 / 2) ∧
      g (2, 0) ≠ 0 ∧
      maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ := by
  rcases NSFormalization.Section3.T20.criticalRegularityT_nonvacuous with
    ⟨ν, g, hg, hν, hnonzero, hsmall, htop⟩
  exact ⟨ν, hν, g, ⟨hg, hsmall⟩, hnonzero, htop⟩

end NSFormalization.Section3.T21.ReviewerNonvacuity

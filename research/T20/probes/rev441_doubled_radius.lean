import NSFormalization.Section3.T20.GlobalRegularity

/- Reviewer-only negative probe: doubling the admissible critical-force radius
must not be discharged by the delivered `globalRegularity` theorem. -/

noncomputable section

namespace NSFormalization.Section3.T20.Rev441

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T20
open scoped ENNReal

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal ((2 * criticalSmallnessH1) * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ := by
  exact globalRegularity

end NSFormalization.Section3.T20.Rev441

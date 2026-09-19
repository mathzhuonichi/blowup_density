import NSFormalization.Section3.T20.Assembly

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T20
open scoped ENNReal

/- Deliberate negative mutation: widen the theorem's force ball from `c * ν`
to `(2 * c) * ν`.  The canonical field must not prove this stronger claim. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal ((2 * criticalRegularityT.c) * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ := by
  intro ν hν g hg hsmall
  exact criticalRegularityT.globalRegularity ν hν g hg hsmall

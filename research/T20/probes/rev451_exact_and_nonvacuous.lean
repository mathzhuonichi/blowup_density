import NSFormalization.Section3.T20.Assembly

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T20
open scoped ENNReal

noncomputable section

example : CriticalRegularityTAPI := criticalRegularityT

example : criticalRegularityStatement := criticalRegularityStatement_holds

example : criticalRegularityT.c = criticalSmallnessH1 := rfl

example : criticalRegularityT.C₀ = criticalTrilinearConst := rfl

example : criticalRegularityT.C₁ = h1TrilinearConst := rfl

example : criticalRegularityT.CH1 = 2 := rfl

example : criticalRegularityT.Ccriterion =
    NSFormalization.Section3.T12.hTwoConst ^ 2 * 2 := by
  change Ccriterion = NSFormalization.Section3.T12.hTwoConst ^ 2 * 2
  rw [Ccriterion, CH1]

example :
    ∃ (ν : ℝ) (g : SpaceTimeField) (_hg : g ∈ forceClassT),
      0 < ν ∧ g (2, 0) ≠ 0 ∧
        criticalRho g < ENNReal.ofReal (criticalRegularityT.c * ν) ∧
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ :=
  criticalRegularityT_nonvacuous

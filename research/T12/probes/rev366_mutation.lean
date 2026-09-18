import NSFormalization.Section3.T12.HaarCube

namespace NSFormalization.Section3.T12
open Set MeasureTheory
open NSFormalization.Section3.T13
open scoped ENNReal

/-- Negative mutation: add the nonzero constant `1` to the whole-space side. -/
example {E : Type*} [NormedAddCommGroup E]
    (w : NavierStokes.ProblemStatement.Space → E)
    (hw : Function.support w ⊆ interior fundamentalCube) (p : ℝ≥0∞) :
    eLpNorm w p (volume.restrict fundamentalCube) = eLpNorm w p volume + 1 := by
  exact eLpNorm_restrict_eq_of_support w hw p

end NSFormalization.Section3.T12

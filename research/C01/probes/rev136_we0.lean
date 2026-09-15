-- Reviewer probe (lane 136 review, REVIEW_E2.md), preserved verbatim; compiles on this branch.
import NSFormalization.Section4.C01.Vocabulary
noncomputable section
open MeasureTheory EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerSmoothLimit
open scoped RealInnerProductSpace ContDiff
namespace Rev136WE
-- E4 sizing: is `wordEnergy 0 = ‖·.toLp‖²` a one-liner?
example (A : SmoothL2Field Space) : wordEnergy 0 A = ‖A.toLp‖ ^ 2 := by
  simp [wordEnergy]
end Rev136WE

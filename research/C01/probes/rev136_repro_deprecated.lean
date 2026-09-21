-- Reviewer probe (lane 136 review, REVIEW_E2.md), preserved verbatim; compiles on this branch.
import NSFormalization.Section4.C01.Vocabulary
open MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerSmoothLimit
open scoped RealInnerProductSpace ContDiff
namespace Repro136b
-- ATTEMPTS_E2.md item 2: the deprecated spelling
example (A : SmoothL2Field Space)
    (hInt : ∀ i : Fin 3, Integrable (fun x => ‖fderiv ℝ A.field x (axis i)‖ ^ 2) volume) :
    (∫ x, ∑ i : Fin 3, ‖fderiv ℝ A.field x (axis i)‖ ^ 2)
      = ∑ i : Fin 3, ∫ x, ‖fderiv ℝ A.field x (axis i)‖ ^ 2 :=
  integral_finset_sum (Finset.univ : Finset (Fin 3)) (fun i _ => hInt i)
end Repro136b

-- Reviewer probe (lane 136 review, REVIEW_E2.md), preserved verbatim; compiles on this branch.
import NSFormalization.Section4.C01.Vocabulary
noncomputable section
open MeasureTheory EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
  EulerSmoothLimit
open scoped RealInnerProductSpace ContDiff
namespace Rev136Dup
-- is `field_normSq_integrable` already a one-liner from Mathlib + the carrier's MemLp?
example (A : SmoothL2Field Space) : Integrable (fun x => ‖A.field x‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm A.smooth.continuous.aestronglyMeasurable).mp A.memLp
-- is `sqrt_dirSum_sq` just `Real.sq_sqrt`?
example (A : SmoothL2Field Space) :
    Real.sqrt (∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2) ^ 2
      = ∑ i : Fin 3, ‖(A.directionalField (axis i)).toLp‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
end Rev136Dup

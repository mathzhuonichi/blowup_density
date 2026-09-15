-- Reviewer probe (lane 136 review, REVIEW_E2.md), preserved verbatim; compiles on this branch.
import Contracts.V1.Data
import Contracts.V1.GradientL6
import NSFormalization.Section4.C01.Vocabulary

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace

namespace Rev136Tail
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data

def gradientSq (z : SpatialField) : ℝ := ∫ x : Space, ‖gradientTensor z x‖ ^ 2

-- attempt 1: pure PiLp.norm_sq_eq_of_L2 under the integral, up to defeq
theorem tail1 (z : SpatialField) :
    gradientSq z = ∫ x : Space, ∑ i : Fin 3, ‖fderiv ℝ z x (EulerOrdinarySobolev.axis i)‖ ^ 2 :=
  integral_congr_ae (Filter.Eventually.of_forall fun x => PiLp.norm_sq_eq_of_L2 _ _)

end Rev136Tail

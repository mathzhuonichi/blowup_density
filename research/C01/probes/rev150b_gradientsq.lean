import Contracts.V1.GradientL6
import Contracts.V1.EnergyAbsorptionPartial

/-! Reviewer probe (lane 150, item 4/5): the ONE remaining vocabulary step between
`C01.energyIdentity_classical_unconditional`'s raw gradient integrand and the spec's
`gradientSq`, on the `verification` side where `gradientTensor` is importable.

Answers: is `PiLp.norm_sq_eq_of_L2` the only step?  -- yes, plus `Finset.sum_congr`. -/

noncomputable section

open MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1 (lift gradientTensor)
open BlowupDensity.Contracts.V1.Data

namespace Rev150b

/-- The spec's `gradientSq` integrand, pointwise, is the raw Frobenius sum the
`formalization` side produces.  One `PiLp.norm_sq_eq_of_L2`. -/
theorem gradientTensor_normSq (z : SpatialField) (x : Space) :
    ‖gradientTensor z x‖ ^ 2
      = ∑ i : Fin 3, ‖fderiv ℝ z x (coordinateVector i)‖ ^ 2 := by
  rw [gradientTensor, spatialGradient, PiLp.norm_sq_eq_of_L2]
  rfl

/-- Hence the integrals agree: the spec's `gradientSq z` is the raw integrand of
`energyIdentity_classical_unconditional` (with `axis i = coordinateVector i`, `rfl`). -/
theorem gradientSq_eq_raw (z : SpatialField) :
    (∫ x : Space, ‖gradientTensor z x‖ ^ 2)
      = ∫ x : Space, ∑ i : Fin 3, ‖fderiv ℝ z x (coordinateVector i)‖ ^ 2 := by
  exact integral_congr_ae (Filter.Eventually.of_forall (gradientTensor_normSq z))

end Rev150b

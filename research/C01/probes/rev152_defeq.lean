import Bindings.EnergyAbsorptionPartialV2

/-! Lane 152 review — the vocabulary identifications the V2 binding relies on. -/

open MeasureTheory
open BlowupDensity.Contracts.V1 (lift gradientTensor)
open BlowupDensity.Contracts.V1.Data
open NavierStokes.ProblemStatement

#check @PiLp.norm_sq_eq_of_L2
#check @BlowupDensity.Contracts.V2.EnergyAbsorptionPartial.gradientSq
#check @BlowupDensity.Bindings.energyAbsorptionPartialV2_gradientSq_eq
#check @BlowupDensity.Bindings.energyAbsorptionPartialV2_pairing_eq
#check @BlowupDensity.Bindings.energyAbsorptionPartial_of_v2

-- the contract's gradient tensor is literally the registered V1 GradientL6 object
example (z : SpatialField) (x : Space) :
    gradientTensor z x = WithLp.toLp 2 (fun i => fderiv ℝ z x (coordinateVector i)) := rfl

-- Frobenius: the tensor norm squared is the sum over the three columns, each column
-- a `Space`-valued vector whose own norm squared is ∑ⱼ|∂ᵢzⱼ|².
example (z : SpatialField) (x : Space) :
    ‖gradientTensor z x‖ ^ 2 = ∑ i : Fin 3, ∑ j : Fin 3,
      |fderiv ℝ z x (coordinateVector i) j| ^ 2 := by
  rw [BlowupDensity.Bindings.energyAbsorptionPartialV2_gradientTensor_normSq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs]

-- the V1 spec-local `slice`/`l2Sq` really are the contract's (drift guard, inherited)
example (z : SpaceTimeField) (t : ℝ) :
    BlowupDensity.Contracts.V1.EnergyAbsorptionPartial.slice z t
      = NSFormalization.Section4.C01.slice z t := rfl
example (z : SpatialField) :
    BlowupDensity.Contracts.V1.EnergyAbsorptionPartial.l2Sq z
      = NSFormalization.Section4.C01.l2Sq z := rfl

-- the docstring's defeq claim: the vendor's `axis` is the contract's `coordinateVector`
example : @EulerOrdinarySobolev.axis = @NavierStokes.ProblemStatement.coordinateVector := rfl

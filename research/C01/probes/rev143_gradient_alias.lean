import NSFormalization.Section4.C01.MomentumCarrierB

/-! Reviewer probe (lane 143): is `gradient` in `MomentumCarrierB`'s open context the
same Mathlib `_root_.gradient` that `energyIdentity_of_carrierB` / `gradient_pairing_zero`
consume?  Reproduces the module's exact `open` list. -/

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerSmoothLimit
open NSFormalization.Source.OrdinaryViscousStability
open NavierStokes.ProblemStatement (temporalDerivative advection spatialLaplacian
  pressureGradient coordinateVector spatialDivergence spatialDerivative VelocityField
  PressureField)
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

#check @gradient
#check @divergence
#check @_root_.gradient
example : @gradient = @_root_.gradient := rfl

-- the `hgrad` slot of the consumer, spelled out
#check @energyIdentity_of_carrierB
#check @gradient_pairing_zero
#check @EulerMeanHarmonic.gradient_coordinate

end NSFormalization.Section4.C01

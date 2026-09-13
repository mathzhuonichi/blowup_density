import Euler.OrdinaryEulerL2Stability
import Euler.OrdinaryPressureCancellation

/-! Sound pressure-gradient adapter for ordinary viscous fields.

Only the pressure gradient is represented in `SmoothL2Field`; no square
integrability of the scalar pressure is assumed. -/
noncomputable section
namespace NSFormalization.Source.OrdinaryViscousGradientAdapter
open EulerSmoothLimit EulerMeanClassical EulerMeanSolenoidal EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open scoped ContDiff

/-- A smooth L² viscous residual which equals a smooth pressure gradient is an
admissible ordinary gradient-space pressure. -/
theorem gradient_mem_of_pressure_gradient
    (A : SmoothL2Field Space) (p : Space → ℝ)
    (hp : ContDiff ℝ ∞ p)
    (hgrad : ∀ x, A.field x = gradient p x) :
    A.toLp ∈ gradientSpace :=
  EulerOrdinarySobolev.gradient_mem A p hp hgrad

end NSFormalization.Source.OrdinaryViscousGradientAdapter

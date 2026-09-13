import Contracts.V1.GradientL6
import NSFormalization.Section4.A05.GradientL6

/-! The only layer that knows the current implementation's names and paths.

`Contracts.V1.GradientL6` is self-contained, so this adapter has two jobs: record
by `rfl` that each notion the specification writes out is the notion the proof
modules use, and assemble the proved estimates into the contract.
-/

noncomputable section
namespace BlowupDensity.Bindings

open MeasureTheory
open NavierStokes.ProblemStatement

section Correspondence

variable (v : Contracts.V1.Data.SpatialField) (j : Fin 3)

/-- The contract's coordinate derivative is the implementation's `∂_j`. -/
theorem partialDeriv_eq :
    Contracts.V1.partialDeriv j v = NSFormalization.Section4.A05.dirDeriv j v := rfl

/-- The contract's gradient tensor is the implementation's `PiLp 2` assembly,
hence also `Contracts.V1.Data.spatialGradient` on the time-independent lift. -/
theorem gradientTensor_eq :
    Contracts.V1.gradientTensor v = NSFormalization.Section4.A05.gradTensor v := rfl

/-- The contract's Laplacian is the implementation's `∑ᵢ ∂ᵢ∂ᵢ`, hence also the
pinned upstream `NavierStokes.ProblemStatement.spatialLaplacian`. -/
theorem laplacian_eq :
    Contracts.V1.laplacian v = NSFormalization.Section4.A05.lap v := rfl

/-- The contract's field class is the implementation's `SmoothL2`. -/
theorem smoothSquareIntegrableJets_eq :
    Contracts.V1.SmoothSquareIntegrableJets v = NSFormalization.Section4.A05.SmoothL2 v := rfl

end Correspondence

/-- Bind the proved gradient-`L⁶` estimate to the stable version-one contract. -/
def gradientL6 : Contracts.V1.GradientL6API where
  Csix := NSFormalization.Section4.A05.gradientL6Const
  Csix_pos := NSFormalization.Section4.A05.gradientL6Const_pos
  hessianLaplacianIdentity := fun _ hv => NSFormalization.Section4.A05.sum_integral_hessian hv
  gradientLSix := fun _ hv => NSFormalization.Section4.A05.eLpNorm_gradTensor_six_le hv

end BlowupDensity.Bindings

import Contracts.V1.Localization
import Bindings.HomogeneousNorm
import NSFormalization.Section3.T13.Assembly

/-!
# Binding for the T13 uniform-localization contract

Every T13 definition restated in the contract is guarded by a whole-function
`rfl` bridge.  The lattice vector is the definition already shared with
`T02.local_potential` and receives a T13-specific bridge name.  No pointwise
bridge is needed: all arguments and codomains are explicit once T01's
registered `PeriodicFrequency` and `SpatialField` aliases are in scope.  The
whole-space homogeneous norm is the registered D01 norm, also checked below by
definitional equality.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open scoped ContDiff ENNReal BigOperators Topology

/-! ## Definitional drift guards -/

theorem fundamentalCube_eq :
    Contracts.V1.fundamentalCube =
      NSFormalization.Section3.T13.fundamentalCube := rfl

theorem supportedInBall_eq :
    Contracts.V1.SupportedInBall =
      NSFormalization.Section3.T13.SupportedInBall := rfl

theorem localization_latticeVector_eq :
    Contracts.V1.latticeVector =
      NSFormalization.Section3.T13.latticeVector := rfl

theorem periodize_eq :
    Contracts.V1.periodize =
      NSFormalization.Section3.T13.periodize := rfl

theorem fractionalRadialKernel_eq :
    Contracts.V1.fractionalRadialKernel =
      NSFormalization.Section3.T13.fractionalRadialKernel := rfl

theorem cFrac_eq :
    Contracts.V1.cFrac =
      NSFormalization.Section3.T13.cFrac := rfl

theorem periodicKernel_eq :
    Contracts.V1.periodicKernel =
      NSFormalization.Section3.T13.periodicKernel := rfl

theorem latticeTail_eq :
    Contracts.V1.latticeTail =
      NSFormalization.Section3.T13.latticeTail := rfl

theorem IReal_eq :
    Contracts.V1.IReal =
      NSFormalization.Section3.T13.IReal := rfl

theorem ITorus_eq :
    Contracts.V1.ITorus =
      NSFormalization.Section3.T13.ITorus := rfl

theorem gradientENorm_eq :
    Contracts.V1.gradientENorm =
      NSFormalization.Section3.T13.gradientENorm := rfl

/-- The whole-space side is exactly the registered D01 datum-infimum norm. -/
theorem localization_dotHomogeneousENorm_eq :
    Contracts.V1.HomogeneousNorm.dotHomogeneousENorm =
      NSFormalization.Section4.D01.dotHomogeneousENorm := rfl

/-! ## The transported six-field record -/

/-- The declaration registered for T13: the proved canonical record,
transported fieldwise through the definitional bridges above. -/
theorem localizationAPI : Contracts.V1.LocalizationAPI := {
  constant_pos_finite :=
    NSFormalization.Section3.T13.localizationAPI.constant_pos_finite
  wholeSpace_identity :=
    NSFormalization.Section3.T13.localizationAPI.wholeSpace_identity
  torus_identity :=
    NSFormalization.Section3.T13.localizationAPI.torus_identity
  localization :=
    NSFormalization.Section3.T13.localizationAPI.localization
  endpoint_zero :=
    NSFormalization.Section3.T13.localizationAPI.endpoint_zero
  endpoint_one :=
    NSFormalization.Section3.T13.localizationAPI.endpoint_one
}

end BlowupDensity.Bindings

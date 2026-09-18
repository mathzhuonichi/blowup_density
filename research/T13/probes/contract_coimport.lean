import Bindings.Localization
import Bindings.LocalPotential

/-! The two T02 V1 contracts can be imported together.  Their shared physical
lattice vector is definitionally identical. -/

example :
    BlowupDensity.Contracts.V1.latticeVector =
      NSFormalization.Section3.T13.latticeVector :=
  BlowupDensity.Bindings.localization_latticeVector_eq

example :
    BlowupDensity.Contracts.V1.latticeVector =
      NSFormalization.Section3.T16.latticeVector :=
  BlowupDensity.Bindings.latticeVector_eq

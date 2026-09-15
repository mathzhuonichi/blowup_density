import Contracts.V1.HomogeneousNorm
import Bindings.HomogeneousNorm
import TestSupport.Axioms

/-! Acceptance test for the registered datum-form homogeneous norm. -/

noncomputable section

namespace BlowupDensity.Tests

/-- The public contract definition is definitionally the proved implementation definition. -/
theorem checkedHomogeneousNorm :
    Contracts.V1.HomogeneousNorm.dotHomogeneousENorm =
      NSFormalization.Section4.D01.dotHomogeneousENorm :=
  Bindings.dotHomogeneousENorm_eq

run_cmd TestSupport.checkAxioms ``checkedHomogeneousNorm

end BlowupDensity.Tests

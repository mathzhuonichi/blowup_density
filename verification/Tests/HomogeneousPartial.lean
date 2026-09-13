import Contracts.V1.HomogeneousPartial
import Bindings.HomogeneousPartial
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification. -/
def checkedHomogeneousPartial :
    Contracts.V1.HomogeneousPartial.HomogeneousApproxPartialAPI :=
  Bindings.homogeneousPartial

run_cmd TestSupport.checkAxioms ``checkedHomogeneousPartial

end BlowupDensity.Tests

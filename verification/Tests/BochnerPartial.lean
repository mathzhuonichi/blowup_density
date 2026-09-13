import Contracts.V1.BochnerPartial
import Bindings.BochnerPartial
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification. -/
def checkedBochnerPartial : Contracts.V1.BochnerPartial.BochnerPartialAPI :=
  Bindings.bochnerPartial

run_cmd TestSupport.checkAxioms ``checkedBochnerPartial

end BlowupDensity.Tests

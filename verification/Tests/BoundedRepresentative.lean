import Contracts.V1.BoundedRepresentative
import Bindings.BoundedRepresentative
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification. -/
def checkedBoundedRepresentative : Contracts.V1.BoundedRep.BoundedRepresentativeAPI :=
  Bindings.boundedRepresentative

run_cmd TestSupport.checkAxioms ``checkedBoundedRepresentative

end BlowupDensity.Tests

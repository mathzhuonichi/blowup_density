import Contracts.V1.TameProduct
import Bindings.TameProduct
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification. -/
def checkedTameProduct : Contracts.V1.TameProduct.TameProductAPI :=
  Bindings.tameProduct

run_cmd TestSupport.checkAxioms ``checkedTameProduct

end BlowupDensity.Tests

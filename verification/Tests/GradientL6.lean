import Contracts.V1.GradientL6
import Bindings.GradientL6
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification. -/
def checkedGradientL6 : Contracts.V1.GradientL6API := Bindings.gradientL6

run_cmd TestSupport.checkAxioms ``checkedGradientL6

end BlowupDensity.Tests

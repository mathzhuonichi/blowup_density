import Contracts.V1.Thresholds
import Bindings.Thresholds
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification. -/
def checkedThresholds : Contracts.V1.ThresholdAPI := Bindings.thresholds

run_cmd TestSupport.checkAxioms ``checkedThresholds

end BlowupDensity.Tests

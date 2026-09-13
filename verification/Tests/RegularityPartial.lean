import Contracts.V1.RegularityPartial
import Bindings.RegularityPartial
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification.
`ManuscriptLocalRegularityPartialAPI` is propositional (both fields are `Prop`),
so this is a `theorem`. -/
theorem checkedRegularityPartial :
    Contracts.V1.RegularityPartial.ManuscriptLocalRegularityPartialAPI :=
  Bindings.regularityPartial

run_cmd TestSupport.checkAxioms ``checkedRegularityPartial

end BlowupDensity.Tests

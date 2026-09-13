import Contracts.V1.Uniqueness
import Bindings.Uniqueness
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification.
`UniquenessAPI` is propositional (both fields are `Prop`), so this is a
`theorem`. -/
theorem checkedUniqueness : Contracts.V1.Uniqueness.UniquenessAPI :=
  Bindings.uniqueness

run_cmd TestSupport.checkAxioms ``checkedUniqueness

end BlowupDensity.Tests

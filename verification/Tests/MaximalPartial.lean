import Contracts.V1.MaximalPartial
import Bindings.MaximalPartial
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification.
`MaximalPartialAPI` is propositional (every field, including the carried
`uniqueness` record, is `Prop`), so this is a `theorem`. -/
theorem checkedMaximalPartial : Contracts.V1.MaximalPartial.MaximalPartialAPI :=
  Bindings.maximalPartial

run_cmd TestSupport.checkAxioms ``checkedMaximalPartial

end BlowupDensity.Tests

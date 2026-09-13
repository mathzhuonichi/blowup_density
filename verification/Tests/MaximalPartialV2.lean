import Contracts.V2.MaximalPartial
import Bindings.MaximalPartialV2
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked.

The version-one test `Tests.MaximalPartial` is untouched and keeps running against
`Bindings.maximalPartial`; this is the second, stronger acceptance test, not a
replacement.  `Bindings.maximalPartial_of_v2` is the checked link between the two:
it projects `Contracts.V1.MaximalPartial.MaximalPartialAPI` out of the version-two
witness, so nothing that version one guarantees is lost by version two.
-/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged version-one
specification **and** the two maximal-solution clauses of lane 064 (`exists_maximal`,
`maximal_unique`).  `MaximalPartialV2API` is propositional (every field, including
the inherited version-one record, is `Prop`), so this is a `theorem`. -/
theorem checkedMaximalPartialV2 : Contracts.V2.MaximalPartial.MaximalPartialV2API :=
  Bindings.maximalPartialV2

run_cmd TestSupport.checkAxioms ``checkedMaximalPartialV2

end BlowupDensity.Tests

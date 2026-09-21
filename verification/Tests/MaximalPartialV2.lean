import Contracts.V2.MaximalPartial
import Bindings.MaximalPartialV2
import TestSupport.Axioms

/-! Exact-type and transitive-axiom checks for current maximal solutions. -/

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

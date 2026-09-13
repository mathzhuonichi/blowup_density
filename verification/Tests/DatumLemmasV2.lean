import Contracts.V2.DatumLemmas
import Bindings.DatumLemmasV2
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked.

The version-one test `Tests.DatumLemmas` is untouched and keeps running against
`Bindings.datumLemmas`; this is the second, stronger acceptance test, not a
replacement.  `Bindings.datumLemmas_of_v2` is the checked link between the two:
it projects `Contracts.V1.DatumLemmas.DatumLemmasAPI` out of the version-two
witness, so nothing that version one guarantees is lost by version two.
-/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged version-one
specification **and** the three half-order finiteness clauses of lane 042 that
make the smallness hypotheses of Propositions 4.3 and 4.4 non-vacuous. -/
def checkedDatumLemmasV2 : Contracts.V2.DatumLemmas.DatumLemmasV2API :=
  Bindings.datumLemmasV2

run_cmd TestSupport.checkAxioms ``checkedDatumLemmasV2

end BlowupDensity.Tests

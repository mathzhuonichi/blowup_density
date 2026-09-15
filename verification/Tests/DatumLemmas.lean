import Contracts.V1.DatumLemmas
import Bindings.DatumLemmas
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification. -/
def checkedDatumLemmas : Contracts.V1.DatumLemmas.DatumLemmasAPI :=
  Bindings.datumLemmas

run_cmd TestSupport.checkAxioms ``checkedDatumLemmas

end BlowupDensity.Tests

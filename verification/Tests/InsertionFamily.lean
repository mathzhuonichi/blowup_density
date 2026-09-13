import Contracts.V1.InsertionFamily
import Bindings.InsertionFamily
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification,
for the given `I03` record and the given reference solution itself:
`A.scaling = S` pins the packet, the correction, the correction force and all
five rescaled fields to the family `I01`, `I02` and `I03` produced, and
`A.a = a` pins the initial velocity, so no other family and no other reference
may be substituted. -/
theorem checkedInsertionFamily : Contracts.V1.insertionFamilyStatement :=
  fun _ν _P S _a R hv hp => ⟨Bindings.insertionFamily S R hv hp, rfl, rfl⟩

run_cmd TestSupport.checkAxioms ``checkedInsertionFamily

end BlowupDensity.Tests

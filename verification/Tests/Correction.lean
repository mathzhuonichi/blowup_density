import Contracts.V1.Correction
import Bindings.Correction
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification,
for the given reference itself: the seven data identities pin the potential, the
correction and the correction force to the prescribed `(v, π, g)`, singular
time, margin and ball, so no extension of the reference may be substituted. -/
theorem checkedCorrection : Contracts.V1.correctionStatement :=
  fun _ν P _T _δ _r _v _π _g x₀ hT hδ hr hv hπ hdiv heq =>
    ⟨Bindings.correction P x₀ hT hδ hr hv hπ hdiv heq,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

run_cmd TestSupport.checkAxioms ``checkedCorrection

end BlowupDensity.Tests

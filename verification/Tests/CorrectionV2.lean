import Contracts.V2.Correction
import Bindings.CorrectionV2
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked.

The version-one test `Tests.Correction` is untouched and keeps running against
`Bindings.correction`; this is the second, stronger acceptance test, not a
replacement.  `Bindings.correctionStatement_of_v2` is the checked link between
the two: it derives `Contracts.V1.correctionStatement` from the statement proved
here, so nothing that version one guarantees is lost by version two.
-/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged version-one
specification **and** place the caller's prescribed compact set `K` inside the
cutoff plateau, for the given reference itself: the seven data identities pin
the potential, the correction and the correction force to the prescribed
`(v, π, g)`, singular time, margin and ball, so no extension of the reference may
be substituted, and `K` is pinned by the record's own type. -/
theorem checkedCorrectionV2 : Contracts.V2.correctionStatement :=
  fun _ν P _K _T _δ _r _v _π _g x₀ hK hT hδ hr hv hπ hdiv heq =>
    ⟨Bindings.correctionV2 P x₀ hK hT hδ hr hv hπ hdiv heq,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

run_cmd TestSupport.checkAxioms ``checkedCorrectionV2

end BlowupDensity.Tests

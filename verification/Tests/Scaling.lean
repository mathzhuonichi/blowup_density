import Contracts.V1.Scaling
import Bindings.Scaling
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification,
for the given `I02` record itself: `A.correction = C` pins the correction, the
correction force, the reference, the singular time, the margin and the ball to
the ones `I02` produced, so no other family may be substituted, and
`A.thresholds = th` pins the exponent arithmetic to the caller's. -/
theorem checkedScaling : Contracts.V1.scalingStatement :=
  fun _ν _P C th => ⟨Bindings.scaling C th, rfl, rfl⟩

run_cmd TestSupport.checkAxioms ``checkedScaling

end BlowupDensity.Tests

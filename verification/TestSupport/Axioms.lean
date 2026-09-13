import Lean

/-! Inspect actual transitive declaration dependencies, not printed output. -/

namespace BlowupDensity.TestSupport
open Lean Elab Command

/-- Reject admissions, native-reduction axioms and project-specific axioms. -/
def checkAxioms (declaration : Name) : CommandElabM Unit := do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let actual ← Lean.collectAxioms declaration
  let unexpected := actual.filter fun name => !permitted.contains name
  unless unexpected.isEmpty do
    throwError "Contract {declaration} depends on forbidden axioms: {unexpected}"
  logInfo m!"Contract {declaration}: checked; standard logical axioms only"

end BlowupDensity.TestSupport

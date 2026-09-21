import NSFormalization.Section3.T11.H1RestartBeyond
import TestSupport.Axioms

#print axioms NSFormalization.Section3.T11.restartBeyondH1T
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.restartBeyondH1T
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.restartBeyondH1T
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"
